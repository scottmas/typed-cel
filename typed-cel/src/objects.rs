use crate::common::ast::{operators, EntryExpr, Expr, IdedExpr};
use crate::common::types::bool::Bool;
use crate::common::types::*;
use crate::common::value::Val;
use crate::context::Context;
use crate::ExecutionError::NoSuchOverload;
use crate::{ExecutionError, Expression, FunctionContext};
use std::any::Any;
use std::borrow::{Borrow, Cow};
use std::cmp::Ordering;
use std::collections::HashMap;
use std::convert::{Infallible, TryFrom, TryInto};
use std::fmt::{Debug, Display, Formatter};
use std::ops;
use std::ops::Deref;
use std::sync::Arc;

#[derive(Debug, PartialEq, Clone)]
pub struct Map {
    pub map: Arc<HashMap<Key, Value>>,
}

impl PartialOrd for Map {
    fn partial_cmp(&self, _: &Self) -> Option<Ordering> {
        None
    }
}

impl Map {
    pub(crate) fn contains_key(&self, key: &(dyn AsKeyRef + '_)) -> bool {
        self.map.contains_key(key)
    }
    /// Returns a reference to the value corresponding to the key.
    ///
    /// `removed: uint` took the cross-kind fallback with it: upstream also tried the same integer
    /// spelled as the OTHER key kind, because `{1: 'a'}[1u]` has to hit. With one integer key
    /// kind there is nothing to reconcile.
    pub fn get(&self, key: &(dyn AsKeyRef + '_)) -> Option<&Value> {
        self.map.get(key)
    }
}

/// A map key. A NUMBER key is a double, like every number, and only an INTEGRAL one can be a key:
/// it is held by its integer value, so it hashes and orders exactly, and it reads back as a
/// `Value::Float`. A fractional double is not a key (`UnsupportedKeyType`), as a double never was.
#[derive(Debug, Eq, PartialEq, Hash, Ord, Clone, PartialOrd)]
pub enum Key {
    Num(i64),
    Bool(bool),
    String(Arc<String>),
}

impl From<CelMapKey> for Key {
    fn from(value: CelMapKey) -> Self {
        match value {
            CelMapKey::Bool(b) => b.into_inner().into(),
            CelMapKey::Num(n) => Key::Num(n.into_inner() as i64),
            CelMapKey::String(s) => s.into_inner().into(),
        }
    }
}

impl From<Key> for CelMapKey {
    fn from(key: Key) -> Self {
        match key {
            Key::Num(i) => CelMapKey::from(i),
            Key::Bool(b) => CelMapKey::from(b),
            Key::String(s) => CelMapKey::from(s.as_str()),
        }
    }
}

/// A borrowed version of [`Key`] that avoids allocating for lookups.
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum KeyRef<'a> {
    Num(i64),
    Bool(bool),
    String(&'a str),
}

/// Trait for converting to a borrowed [`KeyRef`] for efficient lookups.
pub trait AsKeyRef {
    fn as_keyref(&self) -> KeyRef<'_>;
}

impl AsKeyRef for Key {
    fn as_keyref(&self) -> KeyRef<'_> {
        match self {
            Key::Num(i) => KeyRef::Num(*i),
            Key::Bool(b) => KeyRef::Bool(*b),
            Key::String(s) => KeyRef::String(s.as_str()),
        }
    }
}

impl<'a> AsKeyRef for KeyRef<'a> {
    fn as_keyref(&self) -> KeyRef<'a> {
        *self
    }
}

/// Trait object implementations for `dyn AsKeyRef` to enable hashing and comparison.
impl<'a> PartialEq for dyn AsKeyRef + 'a {
    fn eq(&self, other: &Self) -> bool {
        self.as_keyref().eq(&other.as_keyref())
    }
}

impl<'a> Eq for dyn AsKeyRef + 'a {}

impl<'a> std::hash::Hash for dyn AsKeyRef + 'a {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.as_keyref().hash(state)
    }
}

impl<'a> PartialOrd for dyn AsKeyRef + 'a {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<'a> Ord for dyn AsKeyRef + 'a {
    fn cmp(&self, other: &Self) -> Ordering {
        self.as_keyref().cmp(&other.as_keyref())
    }
}

/// Implement `Borrow<dyn AsKeyRef>` for `Key` to enable efficient lookups.
impl<'a> Borrow<dyn AsKeyRef + 'a> for Key {
    fn borrow(&self) -> &(dyn AsKeyRef + 'a) {
        self
    }
}

/// Implement conversions from primitive types to [`Key`]
impl From<String> for Key {
    fn from(v: String) -> Self {
        Key::String(v.into())
    }
}

impl From<Arc<String>> for Key {
    fn from(v: Arc<String>) -> Self {
        Key::String(v)
    }
}

impl<'a> From<&'a str> for Key {
    fn from(v: &'a str) -> Self {
        Key::String(Arc::new(v.into()))
    }
}

impl From<bool> for Key {
    fn from(v: bool) -> Self {
        Key::Bool(v)
    }
}

impl From<i64> for Key {
    fn from(v: i64) -> Self {
        Key::Num(v)
    }
}

impl From<i32> for Key {
    fn from(v: i32) -> Self {
        Key::Num(v as i64)
    }
}

impl From<u32> for Key {
    fn from(v: u32) -> Self {
        Key::Num(v as i64)
    }
}

/// The integer an integral double names as a key, or `None` for one that names no key.
pub(crate) fn integral_key(f: f64) -> Option<i64> {
    (f.fract() == 0.0 && f >= i64::MIN as f64 && f < i64::MAX as f64).then_some(f as i64)
}

impl serde::Serialize for Key {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        match self {
            Key::Num(v) => v.serialize(serializer),
            Key::Bool(v) => v.serialize(serializer),
            Key::String(v) => v.serialize(serializer),
        }
    }
}

impl Display for Key {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Key::Num(v) => write!(f, "{v}"),
            Key::Bool(v) => write!(f, "{v}"),
            Key::String(v) => write!(f, "{v}"),
        }
    }
}

/// Implement conversions from [`Key`] into [`Value`]
impl TryInto<Key> for Value {
    type Error = Value;

    #[inline(always)]
    fn try_into(self) -> Result<Key, Self::Error> {
        match self {
            Value::Float(f) => integral_key(f).map(Key::Num).ok_or(self),
            Value::String(v) => Ok(Key::String(v)),
            Value::Bool(v) => Ok(Key::Bool(v)),
            _ => Err(self),
        }
    }
}

/// Implement conversions from [`KeyRef`] into [`Value`]
impl<'a> TryFrom<&'a Value> for KeyRef<'a> {
    type Error = Value;

    fn try_from(value: &'a Value) -> Result<Self, Self::Error> {
        match value {
            Value::Float(f) => integral_key(*f)
                .map(KeyRef::Num)
                .ok_or_else(|| value.clone()),
            Value::String(v) => Ok(KeyRef::String(v.as_str())),
            Value::Bool(v) => Ok(KeyRef::Bool(*v)),
            _ => Err(value.clone()),
        }
    }
}

// Implement conversion from HashMap<K, V> into CelMap
impl<K: Into<Key>, V: Into<Value>> From<HashMap<K, V>> for Map {
    fn from(map: HashMap<K, V>) -> Self {
        let mut new_map = HashMap::with_capacity(map.len());
        for (k, v) in map {
            new_map.insert(k.into(), v.into());
        }
        Map {
            map: Arc::new(new_map),
        }
    }
}

/// Equality helper for [`Opaque`] values.
///
/// Implementors define how two values of the same runtime type compare for
/// equality when stored as [`Value::Opaque`].
///
/// You normally don't implement this trait manually. It is automatically
/// provided for any `T: Eq + PartialEq + Any + Opaque` (see the blanket impl
/// below). The runtime will first ensure the two values have the same
/// [`Opaque::runtime_type_name`], and only then attempt a downcast and call
/// `Eq::eq`.
pub trait OpaqueEq {
    /// Compare with another [`Opaque`] erased value.
    ///
    /// Implementations should return `false` if `other` does not have the same
    /// runtime type, or if it cannot be downcast to the concrete type of `self`.
    fn opaque_eq(&self, other: &dyn Opaque) -> bool;
}

impl<T> OpaqueEq for T
where
    T: Eq + PartialEq + Any + Opaque,
{
    fn opaque_eq(&self, other: &dyn Opaque) -> bool {
        if self.runtime_type_name() != other.runtime_type_name() {
            return false;
        }
        if let Some(other) = other.downcast_ref::<T>() {
            self.eq(other)
        } else {
            false
        }
    }
}

/// Helper trait to obtain a `&dyn Debug` view.
///
/// This is auto-implemented for any `T: Debug` and is used by the runtime to
/// format [`Opaque`] values without knowing their concrete type.
pub trait AsDebug {
    /// Returns `self` as a `&dyn Debug` trait object.
    fn as_debug(&self) -> &dyn Debug;
}

impl<T> AsDebug for T
where
    T: Debug,
{
    fn as_debug(&self) -> &dyn Debug {
        self
    }
}

/// Trait for user-defined opaque values stored inside [`Value::Opaque`].
///
/// Implement this trait for types that should participate in CEL evaluation as
/// opaque/user-defined values. An opaque value:
/// - must report a stable runtime type name via [`Opaque::runtime_type_name`];
/// - participates in equality via the blanket [`OpaqueEq`] implementation;
/// - can be formatted via [`AsDebug`];
/// - must be thread-safe (`Send + Sync`).
///
/// When the `json` feature is enabled you may optionally provide a JSON
/// representation for diagnostics, logging or interop. Returning `None` keeps the
/// value non-serializable for JSON.
///
/// Example
/// ```rust
/// use std::fmt::{Debug, Formatter, Result as FmtResult};
/// use std::sync::Arc;
/// use typed_cel::fork::objects::{Opaque, Value};
///
/// #[derive(Eq, PartialEq)]
/// struct MyId(u64);
///
/// impl Debug for MyId {
///     fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult { write!(f, "MyId({})", self.0) }
/// }
///
/// impl Opaque for MyId {
///     fn runtime_type_name(&self) -> &str { "example.MyId" }
/// }
///
/// // Values of `MyId` can now be wrapped in `Value::Opaque` and compared.
/// let a = Value::Opaque(Arc::new(MyId(7)));
/// let b = Value::Opaque(Arc::new(MyId(7)));
/// assert_eq!(a, b);
/// ```
pub trait Opaque: Any + OpaqueEq + AsDebug + Send + Sync {
    /// Returns a stable, fully-qualified type name for this value's runtime type.
    ///
    /// This name is used to check type compatibility before attempting downcasts
    /// during equality checks and other operations. It should be stable across
    /// versions and unique within your application or library (e.g., a package
    /// qualified name like `my.pkg.Type`).
    fn runtime_type_name(&self) -> &str;

    /// Optional JSON representation (requires the `json` feature).
    ///
    /// The default implementation returns `None`, indicating that the value
    /// cannot be represented as JSON.
    #[cfg(feature = "json")]
    fn json(&self) -> Option<serde_json::Value> {
        None
    }
}

impl dyn Opaque {
    pub fn downcast_ref<T: Any>(&self) -> Option<&T> {
        let any: &dyn Any = self;
        any.downcast_ref()
    }
}

struct OpaqueVal {
    r#type: Type,
    val: Arc<dyn Opaque>,
}

impl Debug for OpaqueVal {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "OpaqueVal<{}>", self.val.runtime_type_name())
    }
}

impl Val for OpaqueVal {
    fn get_type(&self) -> &Type {
        &self.r#type
    }

    fn equals(&self, other: &dyn Val) -> bool {
        if other.get_type() != self.get_type() {
            false
        } else {
            match other.downcast_ref::<OpaqueVal>() {
                None => false,
                Some(other) => self.val.opaque_eq(other.val.deref()),
            }
        }
    }

    fn clone_as_boxed(&self) -> Box<dyn Val> {
        Box::new(Self {
            r#type: Type::new_opaque_type(self.val.runtime_type_name().to_owned()),
            val: self.val.clone(),
        })
    }
}

impl OpaqueVal {
    fn new(val: Arc<dyn Opaque>) -> Self {
        Self {
            r#type: Type::new_opaque_type(val.runtime_type_name().to_owned()),
            val,
        }
    }

    fn clone_inner(&self) -> Arc<dyn Opaque> {
        self.val.clone()
    }
}

pub trait TryIntoValue {
    type Error: std::error::Error + 'static + Send + Sync;
    fn try_into_value(self) -> Result<Value, Self::Error>;
}

impl<T: serde::Serialize> TryIntoValue for T {
    type Error = crate::ser::SerializationError;
    fn try_into_value(self) -> Result<Value, Self::Error> {
        crate::ser::to_value(self)
    }
}
impl TryIntoValue for Value {
    type Error = Infallible;
    fn try_into_value(self) -> Result<Value, Self::Error> {
        Ok(self)
    }
}

#[derive(Clone)]
pub enum Value {
    List(Arc<Vec<Value>>),
    Map(Map),

    Function(Arc<String>, Option<Box<Value>>),

    // Atoms. ONE number kind: every number at run time is an f64 (`diverges: one numeric type`,
    // `removed: integer values`).
    Float(f64),
    String(Arc<String>),
    Bytes(Arc<Vec<u8>>),
    Bool(bool),
    #[cfg(feature = "chrono")]
    Duration(chrono::Duration),
    Opaque(Arc<dyn Opaque>),
    Null,
}

impl Debug for Value {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::List(l) => write!(f, "List({:?})", l),
            Value::Map(m) => write!(f, "Map({:?})", m),
            Value::Function(name, func) => write!(f, "Function({:?}, {:?})", name, func),
            Value::Float(d) => write!(f, "Float({:?})", d),
            Value::String(s) => write!(f, "String({:?})", s),
            Value::Bytes(b) => write!(f, "Bytes({:?})", b),
            Value::Bool(b) => write!(f, "Bool({:?})", b),
            #[cfg(feature = "chrono")]
            Value::Duration(d) => write!(f, "Duration({:?})", d),
            Value::Opaque(o) => write!(f, "Opaque<{}>({:?})", o.runtime_type_name(), o.as_debug()),
            Value::Null => write!(f, "Null"),
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub enum ValueType {
    List,
    Map,
    Function,
    Float,
    String,
    Bytes,
    Bool,
    Duration,
    Opaque,
    Null,
}

impl Display for ValueType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            ValueType::List => write!(f, "list"),
            ValueType::Map => write!(f, "map"),
            ValueType::Function => write!(f, "function"),
            ValueType::Float => write!(f, "float"),
            ValueType::String => write!(f, "string"),
            ValueType::Bytes => write!(f, "bytes"),
            ValueType::Bool => write!(f, "bool"),
            ValueType::Opaque => write!(f, "opaque"),
            ValueType::Duration => write!(f, "duration"),
            ValueType::Null => write!(f, "null"),
        }
    }
}

impl Value {
    pub fn type_of(&self) -> ValueType {
        match self {
            Value::List(_) => ValueType::List,
            Value::Map(_) => ValueType::Map,
            Value::Function(_, _) => ValueType::Function,
            Value::Float(_) => ValueType::Float,
            Value::String(_) => ValueType::String,
            Value::Bytes(_) => ValueType::Bytes,
            Value::Bool(_) => ValueType::Bool,
            Value::Opaque(_) => ValueType::Opaque,
            #[cfg(feature = "chrono")]
            Value::Duration(_) => ValueType::Duration,
            Value::Null => ValueType::Null,
        }
    }

    pub fn is_zero(&self) -> bool {
        match self {
            Value::List(v) => v.is_empty(),
            Value::Map(v) => v.map.is_empty(),
            Value::Float(f) => *f == 0.0,
            Value::String(v) => v.is_empty(),
            Value::Bytes(v) => v.is_empty(),
            Value::Bool(false) => true,
            #[cfg(feature = "chrono")]
            Value::Duration(v) => v.is_zero(),
            Value::Null => true,
            _ => false,
        }
    }

    pub fn error_expected_type(&self, expected: ValueType) -> ExecutionError {
        ExecutionError::UnexpectedType {
            got: self.type_of().to_string(),
            want: expected.to_string(),
        }
    }
}

impl From<&Value> for Value {
    fn from(value: &Value) -> Self {
        value.clone()
    }
}

impl PartialEq for Value {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Value::Map(a), Value::Map(b)) => a == b,
            (Value::List(a), Value::List(b)) => a == b,
            (Value::Function(a1, a2), Value::Function(b1, b2)) => a1 == b1 && a2 == b2,
            (Value::Float(a), Value::Float(b)) => a == b,
            (Value::String(a), Value::String(b)) => a == b,
            (Value::Bytes(a), Value::Bytes(b)) => a == b,
            (Value::Bool(a), Value::Bool(b)) => a == b,
            (Value::Null, Value::Null) => true,
            #[cfg(feature = "chrono")]
            (Value::Duration(a), Value::Duration(b)) => a == b,
            (Value::Opaque(a), Value::Opaque(b)) => a.opaque_eq(b.deref()),
            (_, _) => false,
        }
    }
}

impl Eq for Value {}

impl PartialOrd for Value {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match (self, other) {
            (Value::Float(a), Value::Float(b)) => a.partial_cmp(b),
            (Value::String(a), Value::String(b)) => Some(a.cmp(b)),
            #[cfg(feature = "chrono")]
            (Value::Duration(a), Value::Duration(b)) => Some(a.cmp(b)),
            _ => None,
        }
    }
}

impl From<&Key> for Value {
    fn from(value: &Key) -> Self {
        match value {
            Key::Num(v) => Value::Float(*v as f64),
            Key::Bool(v) => Value::Bool(*v),
            Key::String(v) => Value::String(v.clone()),
        }
    }
}

impl From<Key> for Value {
    fn from(value: Key) -> Self {
        match value {
            Key::Num(v) => Value::Float(v as f64),
            Key::Bool(v) => Value::Bool(v),
            Key::String(v) => Value::String(v),
        }
    }
}

impl From<&Key> for Key {
    fn from(key: &Key) -> Self {
        key.clone()
    }
}

// Convert Vec<T> to Value
impl<T: Into<Value>> From<Vec<T>> for Value {
    fn from(v: Vec<T>) -> Self {
        Value::List(v.into_iter().map(|v| v.into()).collect::<Vec<_>>().into())
    }
}

// Convert Vec<u8> to Value
impl From<Vec<u8>> for Value {
    fn from(v: Vec<u8>) -> Self {
        Value::Bytes(v.into())
    }
}

#[cfg(feature = "bytes")]
// Convert Bytes to Value
impl From<::bytes::Bytes> for Value {
    fn from(v: ::bytes::Bytes) -> Self {
        Value::Bytes(v.to_vec().into())
    }
}

#[cfg(feature = "bytes")]
// Convert &Bytes to Value
impl From<&::bytes::Bytes> for Value {
    fn from(v: &::bytes::Bytes) -> Self {
        Value::Bytes(v.to_vec().into())
    }
}

// Convert String to Value
impl From<String> for Value {
    fn from(v: String) -> Self {
        Value::String(v.into())
    }
}

impl From<&str> for Value {
    fn from(v: &str) -> Self {
        Value::String(v.to_string().into())
    }
}

// Convert Option<T> to Value
impl<T: Into<Value>> From<Option<T>> for Value {
    fn from(v: Option<T>) -> Self {
        match v {
            Some(v) => v.into(),
            None => Value::Null,
        }
    }
}

// Convert HashMap<K, V> to Value
impl<K: Into<Key>, V: Into<Value>> From<HashMap<K, V>> for Value {
    fn from(v: HashMap<K, V>) -> Self {
        Value::Map(v.into())
    }
}

impl From<ExecutionError> for ResolveResult {
    fn from(value: ExecutionError) -> Self {
        Err(value)
    }
}

pub type ResolveResult = Result<Value, ExecutionError>;

impl From<Value> for ResolveResult {
    fn from(value: Value) -> Self {
        Ok(value)
    }
}

impl TryFrom<&dyn Val> for Value {
    type Error = ExecutionError;
    fn try_from(v: &dyn Val) -> Result<Self, Self::Error> {
        match v.get_type().kind() {
            Kind::Boolean => Ok(Value::Bool(*v.downcast_ref::<CelBool>().unwrap().inner())),
            Kind::Double => Ok(Value::Float(
                *v.downcast_ref::<CelDouble>().unwrap().inner(),
            )),
            Kind::String => Ok(Value::String(Arc::new(
                v.downcast_ref::<CelString>().unwrap().inner().to_string(),
            ))),
            Kind::NullType => Ok(Value::Null),
            Kind::Bytes => Ok(Value::Bytes(Arc::new(
                v.downcast_ref::<CelBytes>().unwrap().inner().to_vec(),
            ))),
            #[cfg(feature = "chrono")]
            Kind::Duration => Ok(Value::Duration(
                *v.downcast_ref::<CelDuration>().unwrap().inner(),
            )),
            Kind::List => {
                let list = v.downcast_ref::<CelList>().unwrap().inner();
                Ok(Value::List(Arc::new(
                    list.iter()
                        .map(|i| i.as_ref().try_into().expect("Not a Value list item"))
                        .collect(),
                )))
            }
            Kind::Map => {
                let map = v.downcast_ref::<CelMap>().unwrap().inner();
                Ok(Value::Map(Map {
                    map: Arc::new(
                        map.iter()
                            .map(|(k, v)| {
                                (
                                    Key::from(k.clone()),
                                    Value::try_from(v.as_ref()).expect("Not a Value map value"),
                                )
                            })
                            .collect(),
                    ),
                }))
            }
            Kind::Opaque => Ok(Value::Opaque(
                v.downcast_ref::<OpaqueVal>().unwrap().clone_inner(),
            )),
            _ => {
                if let Some(opaque) = v.downcast_ref::<OpaqueVal>() {
                    Ok(Value::Opaque(opaque.val.clone()))
                } else {
                    Err(ExecutionError::UnexpectedType {
                        got: v.get_type().name().to_string(),
                        want:
                            "(BOOL|INT|UINT|DOUBLE|STRING|NULL|BYTES|TIMESTAMP|DURATION|LIST|MAP)"
                                .to_string(),
                    })
                }
            }
        }
    }
}

impl TryFrom<Value> for Box<dyn Val> {
    type Error = ExecutionError;
    fn try_from(value: Value) -> Result<Self, Self::Error> {
        match value {
            Value::Bool(b) => Ok(Box::new(CelBool::from(b))),
            Value::Float(f) => Ok(Box::new(CelDouble::from(f))),
            Value::String(s) => Ok(Box::new(CelString::from(s.as_str()))),
            Value::Null => Ok(Box::new(CelNull)),
            Value::Bytes(b) => Ok(Box::new(CelBytes::from(b.as_slice().to_vec()))),
            #[cfg(feature = "chrono")]
            Value::Duration(d) => Ok(Box::new(CelDuration::from(d))),
            Value::List(l) => {
                let result: Result<Vec<Box<dyn Val>>, ExecutionError> =
                    (*l).clone().into_iter().map(|i| i.try_into()).collect();
                Ok(Box::new(CelList::from(result?)))
            }
            Value::Map(map) => {
                let result: Result<HashMap<CelMapKey, Box<dyn Val>>, ExecutionError> = (*map.map)
                    .clone()
                    .into_iter()
                    .map(|(k, v)| v.clone().try_into().map(|v| (k.clone().into(), v)))
                    .collect();
                Ok(Box::new(CelMap::from(result?)))
            }
            Value::Opaque(o) => Ok(Box::new(OpaqueVal::new(o))),
            _ => Err(ExecutionError::UnsupportedTargetType { target: value }),
        }
    }
}

impl Value {
    pub fn resolve_all(expr: &[Expression], ctx: &Context) -> ResolveResult {
        let mut res = Vec::with_capacity(expr.len());
        for expr in expr {
            res.push(Value::resolve(expr, ctx)?);
        }
        Ok(Value::List(res.into()))
    }

    pub fn resolve(expr: &Expression, ctx: &Context) -> ResolveResult {
        Self::resolve_val(expr, ctx)?.as_ref().try_into()
    }

    #[inline(always)]
    pub fn resolve_val<'a>(
        expr: &'a Expression,
        ctx: &'a Context<'a>,
    ) -> Result<Cow<'a, dyn Val>, ExecutionError> {
        match &expr.expr {
            Expr::Literal(literal) => Ok(literal.to_val()),
            Expr::Call(call) => {
                // START OF SPECIAL CASES FOR operators::...
                if call.args.len() == 3 && call.func_name == operators::CONDITIONAL {
                    let cond = Value::resolve_val(&call.args[0], ctx);
                    return if try_bool(cond)? {
                        Value::resolve_val(&call.args[1], ctx)
                    } else {
                        Value::resolve_val(&call.args[2], ctx)
                    };
                }
                if call.args.len() == 2 {
                    match call.func_name.as_str() {
                        operators::LOGICAL_OR => {
                            let left = try_bool(Value::resolve_val(&call.args[0], ctx));
                            return if Ok(true) == left {
                                Ok(Cow::<dyn Val>::Owned(Box::new(CelBool::from(true))))
                            } else {
                                let right = Value::resolve_val(&call.args[1], ctx)?
                                    .downcast_ref::<CelBool>()
                                    .map(|b| *b.inner());
                                match (left, right) {
                                    (Ok(false), Some(right)) => {
                                        Ok(Cow::<dyn Val>::Owned(Box::new(CelBool::from(right))))
                                    }
                                    (Err(_), Some(true)) => {
                                        Ok(Cow::<dyn Val>::Owned(Box::new(CelBool::from(true))))
                                    }
                                    (left, _) => Err(left.err().unwrap_or(NoSuchOverload)),
                                }
                            };
                        }
                        operators::LOGICAL_AND => {
                            let left = try_bool(Value::resolve_val(&call.args[0], ctx));
                            return if Ok(false) == left {
                                Ok(Cow::<dyn Val>::Owned(Box::new(CelBool::from(false))))
                            } else {
                                let right = Value::resolve_val(&call.args[1], ctx)?
                                    .downcast_ref::<CelBool>()
                                    .map(|b| *b.inner());
                                match (left, right) {
                                    (Ok(true), Some(right)) => {
                                        Ok(Cow::<dyn Val>::Owned(Box::new(CelBool::from(right))))
                                    }
                                    (Err(_), Some(false)) => {
                                        Ok(Cow::<dyn Val>::Owned(Box::new(CelBool::from(false))))
                                    }
                                    (left, _) => Err(left.err().unwrap_or(NoSuchOverload)),
                                }
                            };
                        }
                        operators::EQUALS => {
                            return Ok(bool(
                                Value::resolve_val(&call.args[0], ctx)?
                                    .eq(&Value::resolve_val(&call.args[1], ctx)?),
                            ))
                        }
                        operators::NOT_EQUALS => {
                            return Ok(bool(
                                Value::resolve_val(&call.args[0], ctx)?
                                    .ne(&Value::resolve_val(&call.args[1], ctx)?),
                            ))
                        }
                        operators::INDEX => {
                            let value = Value::resolve_val(&call.args[0], ctx)?;
                            let index = Self::resolve_val(&call.args[1], ctx)?;
                            return match value {
                                Cow::Borrowed(val) => val
                                    .as_indexer()
                                    .ok_or(ExecutionError::NoSuchOverload)?
                                    .get(index.as_ref()),
                                Cow::Owned(val) => val
                                    .into_indexer()
                                    .ok_or(ExecutionError::NoSuchOverload)?
                                    .steal(index.as_ref())
                                    .map(Cow::Owned),
                            };
                        }
                        // END OF SPECIAL CASES

                        // all below is NOT special in the interpreter
                        operators::ADD => {
                            let lhs = Value::resolve_val(&call.args[0], ctx)?;
                            let rhs = Value::resolve_val(&call.args[1], ctx)?;
                            return Ok(Cow::Owned(
                                lhs.as_ref()
                                    .as_adder()
                                    .ok_or_else(|| {
                                        ExecutionError::UnsupportedBinaryOperator(
                                            "add",
                                            lhs.as_ref().try_into().unwrap_or(Value::Null),
                                            rhs.as_ref().try_into().unwrap_or(Value::Null),
                                        )
                                    })?
                                    .add(rhs.as_ref())?
                                    .into_owned(),
                            ));
                        }
                        operators::SUBSTRACT => {
                            let lhs = Value::resolve_val(&call.args[0], ctx)?;
                            let rhs = Value::resolve_val(&call.args[1], ctx)?;
                            return Ok(Cow::Owned(
                                lhs.as_subtractor()
                                    .ok_or_else(|| {
                                        ExecutionError::UnsupportedBinaryOperator(
                                            "sub",
                                            lhs.as_ref().try_into().unwrap_or(Value::Null),
                                            rhs.as_ref().try_into().unwrap_or(Value::Null),
                                        )
                                    })?
                                    .sub(rhs.as_ref())?
                                    .into_owned(),
                            ));
                        }
                        operators::DIVIDE => {
                            let lhs = Value::resolve_val(&call.args[0], ctx)?;
                            let rhs = Value::resolve_val(&call.args[1], ctx)?;
                            return Ok(Cow::Owned(
                                lhs.as_divider()
                                    .ok_or_else(|| {
                                        ExecutionError::UnsupportedBinaryOperator(
                                            "div",
                                            lhs.as_ref().try_into().unwrap_or(Value::Null),
                                            rhs.as_ref().try_into().unwrap_or(Value::Null),
                                        )
                                    })?
                                    .div(rhs.as_ref())?
                                    .into_owned(),
                            ));
                        }
                        operators::MULTIPLY => {
                            let lhs = Value::resolve_val(&call.args[0], ctx)?;
                            let rhs = Value::resolve_val(&call.args[1], ctx)?;
                            return Ok(Cow::Owned(
                                lhs.as_multiplier()
                                    .ok_or_else(|| {
                                        ExecutionError::UnsupportedBinaryOperator(
                                            "mul",
                                            lhs.as_ref().try_into().unwrap_or(Value::Null),
                                            rhs.as_ref().try_into().unwrap_or(Value::Null),
                                        )
                                    })?
                                    .mul(rhs.as_ref())?
                                    .into_owned(),
                            ));
                        }
                        operators::LESS => {
                            let lhs = Value::resolve_val(&call.args[0], ctx)?;
                            let rhs = Value::resolve_val(&call.args[1], ctx)?;
                            return Ok(bool(
                                lhs.as_comparer()
                                    .ok_or(ExecutionError::NoSuchOverload)?
                                    .compare(rhs.as_ref())?
                                    == Ordering::Less,
                            ));
                        }
                        operators::LESS_EQUALS => {
                            let lhs = Value::resolve_val(&call.args[0], ctx)?;
                            let rhs = Value::resolve_val(&call.args[1], ctx)?;
                            return if lhs
                                .as_comparer()
                                .ok_or(ExecutionError::NoSuchOverload)?
                                .compare(rhs.as_ref())?
                                == Ordering::Greater
                            {
                                Ok(bool(false))
                            } else {
                                Ok(bool(true))
                            };
                        }
                        operators::GREATER => {
                            let lhs = Value::resolve_val(&call.args[0], ctx)?;
                            let rhs = Value::resolve_val(&call.args[1], ctx)?;
                            return Ok(bool(
                                lhs.as_comparer()
                                    .ok_or(ExecutionError::NoSuchOverload)?
                                    .compare(rhs.as_ref())?
                                    == Ordering::Greater,
                            ));
                        }
                        operators::GREATER_EQUALS => {
                            let lhs = Value::resolve_val(&call.args[0], ctx)?;
                            let rhs = Value::resolve_val(&call.args[1], ctx)?;
                            return if lhs
                                .as_comparer()
                                .ok_or(ExecutionError::NoSuchOverload)?
                                .compare(rhs.as_ref())?
                                == Ordering::Less
                            {
                                Ok(bool(false))
                            } else {
                                Ok(bool(true))
                            };
                        }
                        operators::IN => {
                            let lhs = Value::resolve_val(&call.args[0], ctx)?;
                            let rhs = Value::resolve_val(&call.args[1], ctx)?;
                            if let Some(lazy) = rhs.downcast_ref::<crate::lazy::LazyAdapter>() {
                                let name = lhs
                                    .downcast_ref::<CelString>()
                                    .ok_or(ExecutionError::NoSuchOverload)?;
                                return Ok(bool(lazy.presence(name.inner())?));
                            }
                            return if let Some(container) = rhs.as_container() {
                                Ok(bool(container.contains(lhs.as_ref())?))
                            } else {
                                Err(ExecutionError::NoSuchOverload)
                            };
                        }
                        _ => (),
                    }
                }
                if call.args.len() == 1 {
                    match call.func_name.as_str() {
                        operators::LOGICAL_NOT => {
                            let expr = Value::resolve_val(&call.args[0], ctx)?;
                            return expr
                                .downcast_ref::<CelBool>()
                                .map(Bool::negate)
                                .ok_or(ExecutionError::NoSuchOverload)
                                .map(|b| bool(b.into_inner()));
                        }
                        operators::NEGATE => {
                            let val = Value::resolve_val(&call.args[0], ctx)?;
                            return Ok(Cow::<dyn Val>::Owned(
                                val.as_negator()
                                    .ok_or(ExecutionError::NoSuchOverload)?
                                    .negate()?,
                            ));
                        }
                        operators::NOT_STRICTLY_FALSE => {
                            return Ok(bool(
                                try_bool(Value::resolve_val(&call.args[0], ctx)).unwrap_or(true),
                            ));
                        }
                        _ => (),
                    }
                }
                match &call.target {
                    None => {
                        // TODO: Optimize for the 1 and 2 arg cases and avoid the Vec altogether
                        let args: Result<Vec<Cow<dyn Val>>, ExecutionError> = call
                            .args
                            .iter()
                            .map(|a| Value::resolve_val(a, ctx))
                            .collect();
                        let args = args?;
                        if let Some(op) = ctx.env().find_overload(&call.func_name, &args) {
                            return op(args);
                        }
                        let func = ctx.get_function(call.func_name.as_str()).ok_or_else(|| {
                            ExecutionError::UndeclaredReference(call.func_name.clone().into())
                        })?;
                        let mut ctx = FunctionContext::new(&call.func_name, None, ctx, args);
                        let v = (func)(&mut ctx)?;
                        Ok(Cow::<dyn Val>::Owned(TryInto::<Box<dyn Val>>::try_into(v)?))
                    }
                    Some(target) => {
                        let args: Result<Vec<Cow<dyn Val>>, ExecutionError> = call
                            .args
                            .iter()
                            .map(|a| Value::resolve_val(a, ctx))
                            .collect();
                        let args = args?;
                        let qualified_func = match &target.expr {
                            Expr::Ident(prefix) => {
                                let qualified_name = format!("{prefix}.{}", call.func_name);
                                if let Some(op) = ctx.env().find_overload(&qualified_name, &args) {
                                    return op(args);
                                }
                                ctx.get_function(&qualified_name)
                            }
                            _ => None,
                        };
                        let (target, func, args) = match qualified_func {
                            None => {
                                let target = Value::resolve_val(target, ctx)?;
                                let mut args = args;
                                args.insert(0, target);
                                if let Some(op) =
                                    ctx.env().find_member_overload(&call.func_name, &args)
                                {
                                    return op(args);
                                }
                                let target = args.remove(0);
                                let func =
                                    ctx.get_function(call.func_name.as_str()).ok_or_else(|| {
                                        ExecutionError::UndeclaredReference(
                                            call.func_name.clone().into(),
                                        )
                                    })?;
                                (Some(target), func, args)
                            }
                            Some(func) => (None, func, args),
                        };
                        let mut ctx = FunctionContext::new(&call.func_name, target, ctx, args);
                        // todo fix this to _not_ use `Value`
                        let v = (func)(&mut ctx)?;
                        Ok(Cow::<dyn Val>::Owned(TryInto::<Box<dyn Val>>::try_into(v)?))
                    }
                }
            }
            Expr::Ident(name) => Ok(ctx
                .get_variable(name)
                .ok_or_else(|| ExecutionError::UndeclaredReference(Arc::new(name.to_string())))?),
            Expr::Select(select) => {
                let left = Value::resolve_val(select.operand.deref(), ctx)?;
                let key: CelString = select.field.as_str().into();

                if select.test {
                    if let Some(lazy) = left.downcast_ref::<crate::lazy::LazyAdapter>() {
                        return Ok(bool(lazy.presence(key.inner())?));
                    }
                    match left.get_type().kind() {
                        Kind::Map => Ok(bool(
                            left.as_container()
                                .ok_or_else(|| {
                                    ExecutionError::NoSuchKey(Arc::new(key.inner().to_string()))
                                })?
                                .contains(&key)?,
                        )),
                        _ => Ok(Cow::<dyn Val>::Owned(
                            left.as_indexer()
                                .ok_or_else(|| ExecutionError::NoSuchOverload)?
                                .get(&key)?
                                .into_owned(),
                        )),
                    }
                } else {
                    match left.get_type().kind() {
                        Kind::Map => {
                            // todo avoid cloning when not needed
                            Ok(Cow::<dyn Val>::Owned(
                                left.as_indexer()
                                    .ok_or_else(|| {
                                        ExecutionError::NoSuchKey(Arc::new(key.inner().to_string()))
                                    })?
                                    .get(&key)?
                                    .into_owned(),
                            ))
                        }
                        _ => Ok(Cow::<dyn Val>::Owned(
                            left.as_indexer()
                                .ok_or_else(|| ExecutionError::NoSuchOverload)?
                                .get(&key)?
                                .into_owned(),
                        )),
                    }
                }
            }
            Expr::List(list_expr) => {
                let list = list_expr
                    .elements
                    .iter()
                    .map(|element| Value::resolve_val(element, ctx).map(Cow::into_owned))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(Cow::<dyn Val>::Owned(Box::new(CelList::from(list))))
            }
            Expr::Map(map_expr) => {
                let mut map = HashMap::with_capacity(map_expr.entries.len());
                for entry in map_expr.entries.iter() {
                    let EntryExpr::MapEntry(e) = &entry.expr;
                    let key: CelMapKey =
                        Value::resolve_val(&e.key, ctx)?.into_owned().try_into()?;
                    // todo do not clone if not needed!
                    map.insert(key, Value::resolve_val(&e.value, ctx)?.into_owned());
                }
                let map: Box<CelMap> = CelMap::from(map).into();
                Ok(Cow::<dyn Val>::Owned(map))
            }
            Expr::Comprehension(comprehension) => {
                let accu_init = Value::resolve_val(&comprehension.accu_init, ctx)?;
                let iter = Value::resolve_val(&comprehension.iter_range, ctx)?;
                let mut ctx = ctx.new_inner_scope();
                ctx.add_variable_as_val(&comprehension.accu_var, accu_init.clone_as_boxed());

                let mut items = iter
                    .as_iterable()
                    .ok_or(ExecutionError::NoSuchOverload)?
                    .iter();
                // The accumulator can be an ERROR, and the loop keeps going when it is. `all()`'s
                // loop condition is `@not_strictly_false(@result)`, which an error passes — that is
                // what lets a LATER element's `false` absorb an EARLIER element's error, so
                // `[1, 2, 3].all(e, {1: true, 3: false}[e])` is `false` rather than the missing key
                // at `e == 2`.
                //
                // Upstream `?`-propagated the step, which ended the loop at the error and made the
                // absorbing element unreachable. This fork has no error VALUE to bind to `@result`,
                // so the error is carried beside the accumulator instead.
                let mut pending: Option<ExecutionError> = None;
                while let Some(item) = items.next() {
                    if pending.is_none()
                        && !try_bool(Value::resolve_val(&comprehension.loop_cond, &ctx))?
                    {
                        break;
                    }
                    ctx.add_variable_as_val(&comprehension.iter_var, item.clone_as_boxed());
                    match Value::resolve_val(&comprehension.loop_step, &ctx) {
                        Ok(accu) => {
                            if absorbs(&comprehension.loop_step, accu.as_ref()) {
                                pending = None;
                            }
                            ctx.add_variable_as_val(&comprehension.accu_var, accu.clone_as_boxed());
                        }
                        // The FIRST error is the one reported, which is what `?` did.
                        Err(e) => {
                            if pending.is_none() {
                                pending = Some(e);
                            }
                        }
                    }
                }
                if let Some(e) = pending {
                    return Err(e);
                }
                Ok(Cow::<dyn Val>::Owned(
                    Value::resolve_val(&comprehension.result, &ctx)?.into_owned(),
                ))
            }
            Expr::Unspecified => panic!("Can't evaluate Unspecified Expr"),
        }
    }
}

/// Does `accu` DETERMINE the answer of `step`, absorbing an error the accumulator was carrying?
///
/// Only a determining value absorbs. `false` settles `&&` and `true` settles `||`, whatever the
/// other operand did; anything else leaves the error deciding. So `[2, 1].all(e, …)` — error, then
/// TRUE — is still an error: a later `true` is not an answer, it is just another operand.
///
/// This reads the step's operator out of the AST, which is the one place that knows which value is
/// absorbing. A comprehension whose step is not a logical operator — `map`, `filter`, whose
/// accumulator is a list rather than a truth value — has no absorbing value at all, and an error in
/// one of its elements must still propagate.
fn absorbs(step: &IdedExpr, accu: &dyn Val) -> bool {
    let Expr::Call(call) = &step.expr else {
        return false;
    };
    let Some(value) = accu.downcast_ref::<CelBool>().map(|b| *b.inner()) else {
        return false;
    };
    match call.func_name.as_str() {
        operators::LOGICAL_AND => !value,
        operators::LOGICAL_OR => value,
        _ => false,
    }
}

fn bool<'a>(boolean: bool) -> Cow<'a, dyn Val> {
    Cow::<dyn Val>::Owned(Box::new(CelBool::from(boolean)))
}

fn try_bool(val: Result<Cow<dyn Val>, ExecutionError>) -> Result<bool, ExecutionError> {
    match val {
        Ok(val) => val
            .downcast_ref::<CelBool>()
            .map(|b| *b.inner())
            .ok_or(ExecutionError::NoSuchOverload),
        Err(err) => Result::Err(err),
    }
}

impl ops::Add<Value> for Value {
    type Output = ResolveResult;

    #[inline(always)]
    fn add(self, rhs: Value) -> Self::Output {
        match (self, rhs) {
            (Value::Float(l), Value::Float(r)) => Value::Float(l + r).into(),

            (Value::List(mut l), Value::List(mut r)) => {
                {
                    // If this is the only reference to `l`, we can append to it in place.
                    // `l` is replaced with a clone otherwise.
                    let l = Arc::make_mut(&mut l);

                    // Likewise, if this is the only reference to `r`, we can move its values
                    // instead of cloning them.
                    match Arc::get_mut(&mut r) {
                        Some(r) => l.append(r),
                        None => l.extend(r.iter().cloned()),
                    }
                }

                Ok(Value::List(l))
            }
            (Value::String(mut l), Value::String(r)) => {
                // If this is the only reference to `l`, we can append to it in place.
                // `l` is replaced with a clone otherwise.
                Arc::make_mut(&mut l).push_str(&r);
                Ok(Value::String(l))
            }
            #[cfg(feature = "chrono")]
            (Value::Duration(l), Value::Duration(r)) => l
                .checked_add(&r)
                .ok_or_else(|| ExecutionError::Overflow("add", l.into(), r.into()))
                .map(Value::Duration),
            (left, right) => Err(ExecutionError::UnsupportedBinaryOperator(
                "add", left, right,
            )),
        }
    }
}

impl ops::Sub<Value> for Value {
    type Output = ResolveResult;

    #[inline(always)]
    fn sub(self, rhs: Value) -> Self::Output {
        match (self, rhs) {
            (Value::Float(l), Value::Float(r)) => Value::Float(l - r).into(),

            #[cfg(feature = "chrono")]
            (Value::Duration(l), Value::Duration(r)) => l
                .checked_sub(&r)
                .ok_or_else(|| ExecutionError::Overflow("sub", l.into(), r.into()))
                .map(Value::Duration),
            (left, right) => Err(ExecutionError::UnsupportedBinaryOperator(
                "sub", left, right,
            )),
        }
    }
}

impl ops::Div<Value> for Value {
    type Output = ResolveResult;

    #[inline(always)]
    fn div(self, rhs: Value) -> Self::Output {
        match (self, rhs) {
            (Value::Float(l), Value::Float(r)) => Value::Float(l / r).into(),

            (left, right) => Err(ExecutionError::UnsupportedBinaryOperator(
                "div", left, right,
            )),
        }
    }
}

impl ops::Mul<Value> for Value {
    type Output = ResolveResult;

    #[inline(always)]
    fn mul(self, rhs: Value) -> Self::Output {
        match (self, rhs) {
            (Value::Float(l), Value::Float(r)) => Value::Float(l * r).into(),

            (left, right) => Err(ExecutionError::UnsupportedBinaryOperator(
                "mul", left, right,
            )),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{objects::Key, Context, ExecutionError, Program, Value};
    use std::collections::HashMap;
    use std::sync::Arc;

    #[test]
    fn test_indexed_map_access() {
        let mut context = Context::default();
        let mut headers = HashMap::new();
        headers.insert("Content-Type", "application/json".to_string());
        context.add_variable_from_value("headers", headers);

        let program = Program::compile("headers[\"Content-Type\"]").unwrap();
        let value = program.execute(&context).unwrap();
        assert_eq!(value, "application/json".into());
    }

    #[test]
    fn test_heterogeneous_compare() {
        let context = Context::default();

        let program = Program::compile("1 < 1.1").unwrap();
        let value = program.execute(&context).unwrap();
        assert_eq!(value, true.into());

        let program = Program::compile("0 > -10").unwrap();
        let value = program.execute(&context).unwrap();
        assert_eq!(value, true.into());
    }

    #[test]
    fn test_float_compare() {
        let context = Context::default();

        let program = Program::compile("1.0 > 0.0").unwrap();
        let value = program.execute(&context).unwrap();
        assert_eq!(value, true.into());

        let program = Program::compile("0.0 / 0.0 == 0.0 / 0.0").unwrap();
        let value = program.execute(&context).unwrap();
        assert_eq!(value, false.into(), "NaN should not equal itself");

        let program = Program::compile("1.0 > 0.0 / 0.0").unwrap();
        let result = program.execute(&context);
        assert!(
            result.is_err(),
            "NaN should not be comparable with inequality operators"
        );
    }

    #[test]
    fn test_invalid_compare() {
        let context = Context::default();

        let program = Program::compile("{} == []").unwrap();
        let value = program.execute(&context).unwrap();
        assert_eq!(value, false.into());
    }

    #[test]
    fn test_size_fn_var() {
        let program = Program::compile("size(requests) + size == 5").unwrap();
        let mut context = Context::default();
        let requests = vec![Value::Float(42.0), Value::Float(42.0)];
        context
            .add_variable("requests", Value::List(Arc::new(requests)))
            .unwrap();
        context.add_variable("size", Value::Float(3.0)).unwrap();
        assert_eq!(program.execute(&context).unwrap(), Value::Bool(true));
    }

    fn test_execution_error(program: &str, expected: ExecutionError) {
        let program = Program::compile(program).unwrap();
        let result = program.execute(&Context::default());
        assert_eq!(result.unwrap_err(), expected);
    }

    #[test]
    fn test_invalid_sub() {
        test_execution_error(
            "'foo' - 10",
            ExecutionError::UnsupportedBinaryOperator("sub", "foo".into(), Value::Float(10.0)),
        );
    }

    #[test]
    fn test_invalid_add() {
        test_execution_error(
            "'foo' + 10",
            ExecutionError::UnsupportedBinaryOperator("add", "foo".into(), Value::Float(10.0)),
        );
    }

    #[test]
    fn test_invalid_div() {
        test_execution_error(
            "'foo' / 10",
            ExecutionError::UnsupportedBinaryOperator("div", "foo".into(), Value::Float(10.0)),
        );
    }

    #[test]
    fn out_of_bound_list_access() {
        let program = Program::compile("list[10]").unwrap();
        let mut context = Context::default();
        context
            .add_variable("list", Value::List(Arc::new(vec![])))
            .unwrap();
        let result = program.execute(&context);
        assert_eq!(
            result,
            Err(ExecutionError::IndexOutOfBounds(Value::Float(10.0)))
        );
    }

    #[test]
    fn out_of_bound_list_access_negative() {
        let program = Program::compile("list[-1]").unwrap();
        let mut context = Context::default();
        context
            .add_variable("list", Value::List(Arc::new(vec![])))
            .unwrap();
        let result = program.execute(&context);
        assert_eq!(
            result,
            Err(ExecutionError::IndexOutOfBounds(Value::Float(-1.0)))
        );
    }

    #[test]
    fn reference_to_value() {
        let test = "example".to_string();
        let direct: Value = test.as_str().into();
        assert_eq!(direct, Value::String(Arc::new(String::from("example"))));

        let vec = vec![test.as_str()];
        let indirect: Value = vec.into();
        assert_eq!(
            indirect,
            Value::List(Arc::new(vec![Value::String(Arc::new(String::from(
                "example"
            )))]))
        );
    }

    #[test]
    fn test_short_circuit_and() {
        let mut context = Context::default();
        let data: HashMap<String, String> = HashMap::new();
        context.add_variable_from_value("data", data);

        let program = Program::compile("has(data.x) && data.x.startsWith(\"foo\")").unwrap();
        let value = program.execute(&context);
        println!("{value:?}");
        assert!(
            value.is_ok(),
            "The AND expression should support short-circuit evaluation."
        );
    }

    #[test]
    fn test_or_ignores_err_when_short_circuiting() {
        let mut context = Context::default();
        context.add_variable_from_value("foo", 42);
        context.add_variable_from_value("bar", 42);
        let program = Program::compile("foo || bar > 0").unwrap();
        let value = program.execute(&context);
        assert_eq!(value, Ok(true.into()));

        let program = Program::compile("foo || bar < 0").unwrap();
        let value = program.execute(&context);
        assert!(value.is_err());
    }

    #[test]
    fn test_and_ignores_err_when_short_circuiting() {
        let mut context = Context::default();
        context.add_variable_from_value("foo", 42);
        context.add_variable_from_value("bar", 42);
        let program = Program::compile("foo && bar < 0").unwrap();
        let value = program.execute(&context);
        assert_eq!(value, Ok(false.into()));

        let program = Program::compile("foo && bar > 0").unwrap();
        let value = program.execute(&context);
        assert!(value.is_err());
    }

    /// `removed: integer values`: what was checked i64 arithmetic is IEEE double arithmetic.
    /// Nothing overflows and nothing divides by zero — `1 / 0` is `+inf`.
    #[test]
    fn number_math_is_double_math() {
        let context = Context::default();
        for (expr, want) in [
            ("1 / 0", f64::INFINITY),
            ("7 / 2", 3.5),
            (&format!("{} + 1", i64::MAX), i64::MAX as f64 + 1.0),
            (&format!("{} * 2", i64::MAX), i64::MAX as f64 * 2.0),
        ] {
            let got = Program::compile(expr).unwrap().execute(&context);
            assert_eq!(got, Ok(Value::Float(want)), "{expr}");
        }
    }

    #[test]
    fn test_index_missing_map_key() {
        let mut ctx = Context::default();
        let mut map = HashMap::new();
        map.insert("a".to_string(), Value::Float(1.0));
        ctx.add_variable_from_value("mymap", map);

        let p = Program::compile(r#"mymap["missing"]"#).expect("Must compile");
        let result = p.execute(&ctx);

        assert!(result.is_err(), "Should error on missing map key");
    }

    mod opaque {
        use crate::objects::{Map, Opaque, OpaqueVal};
        use crate::parser::Parser;
        use crate::{Context, ExecutionError, FunctionContext, Program, Value};
        use serde::Serialize;
        use std::collections::HashMap;
        use std::fmt::Debug;
        use std::ops::Deref;
        use std::sync::Arc;

        #[derive(Debug, Eq, PartialEq, Serialize)]
        struct MyStruct {
            field: String,
        }

        impl Opaque for MyStruct {
            fn runtime_type_name(&self) -> &str {
                "my_struct"
            }

            #[cfg(feature = "json")]
            fn json(&self) -> Option<serde_json::Value> {
                Some(serde_json::to_value(self).unwrap())
            }
        }

        #[test]
        fn test_opaque_fn() {
            pub fn my_fn(ftx: &FunctionContext) -> Result<Value, ExecutionError> {
                if let Some(Some(opaque)) = ftx.this.as_ref().map(|v| v.downcast_ref::<OpaqueVal>())
                {
                    if opaque.val.runtime_type_name() == "my_struct" {
                        Ok(opaque
                            .val
                            .deref()
                            .downcast_ref::<MyStruct>()
                            .unwrap()
                            .field
                            .clone()
                            .into())
                    } else {
                        Err(ExecutionError::UnexpectedType {
                            got: opaque.val.runtime_type_name().to_string(),
                            want: "my_struct".to_string(),
                        })
                    }
                } else {
                    Err(ExecutionError::UnexpectedType {
                        got: format!("{:?}", ftx.this),
                        want: "Value::Opaque".to_string(),
                    })
                }
            }

            let value = Arc::new(MyStruct {
                field: String::from("value"),
            });

            let mut ctx = Context::default();
            ctx.add_variable_from_value("mine", Value::Opaque(value.clone()));
            ctx.add_function("myFn", my_fn);
            let prog = Program::compile("mine.myFn()").unwrap();
            assert_eq!(
                Ok(Value::String(Arc::new("value".into()))),
                prog.execute(&ctx)
            );
        }

        #[test]
        fn opaque_eq() {
            let value_1 = Arc::new(MyStruct {
                field: String::from("1"),
            });
            let value_2 = Arc::new(MyStruct {
                field: String::from("2"),
            });

            let mut ctx = Context::default();
            ctx.add_variable_from_value("v1", Value::Opaque(value_1.clone()));
            ctx.add_variable_from_value("v1b", Value::Opaque(value_1));
            ctx.add_variable_from_value("v2", Value::Opaque(value_2));
            assert_eq!(
                Program::compile("v2 == v1").unwrap().execute(&ctx),
                Ok(false.into())
            );
            assert_eq!(
                Program::compile("v1 == v1b").unwrap().execute(&ctx),
                Ok(true.into())
            );
            assert_eq!(
                Program::compile("v2 == v2").unwrap().execute(&ctx),
                Ok(true.into())
            );
        }

        #[test]
        fn test_value_holder_dbg() {
            let opaque = Arc::new(MyStruct {
                field: "not so opaque".to_string(),
            });
            let opaque = Value::Opaque(opaque);
            assert_eq!(
                "Opaque<my_struct>(MyStruct { field: \"not so opaque\" })",
                format!("{:?}", opaque)
            );
        }

        #[test]
        #[cfg(feature = "json")]
        fn test_json() {
            let value = Arc::new(MyStruct {
                field: String::from("value"),
            });
            let cel_value = Value::Opaque(value);
            let mut map = serde_json::Map::new();
            map.insert(
                "field".to_string(),
                serde_json::Value::String("value".to_string()),
            );
            assert_eq!(
                cel_value.json().expect("Must convert"),
                serde_json::Value::Object(map)
            );
        }
    }
}
