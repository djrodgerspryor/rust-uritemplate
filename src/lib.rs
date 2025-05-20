//! `rust-uritemplate` is a Rust implementation of
//! [RFC6570  - URI Template](http://tools.ietf.org/html/rfc6570) that can
//! process URI Templates up to and including ones designated as Level 4 by the
//! specification. It passes all of the tests in the
//! [uritemplate-test](https://github.com/uri-templates/uritemplate-test) test
//! suite.
//!
//! Basic Usage
//! -----------
//! Variable setting can be chained for nice, clean code.
//!
//! ```ignore
//! extern crate uritemplate;
//! use uritemplate::UriTemplate;
//!
//! let uri = UriTemplate::new("/view/{object:1}/{/object,names}{?query*}")
//!     .set("object", "lakes")
//!     .set("names", &["Erie", "Superior", "Ontario"])
//!     .set("query", &[("size", "15"), ("lang", "en")])
//!     .build();
//!
//! assert_eq!(uri, "/view/l/lakes/Erie,Superior,Ontario?size=15&lang=en");
//! ```
//!
//! It is not possible to set a variable to the value "undefined". Instead,
//! simply delete the variable if you have already set it.
//!
//! ```ignore
//! let mut t = UriTemplate::new("{hello}");
//! t.set("hello", "Hello World!");
//! assert_eq!(t.build(), "Hello%20World%21");
//!
//! t.delete("hello");
//! assert_eq!(t.build(), "");
//! ```
//!
//! The `delete` function returns `true` if the variable existed and `false`
//! otherwise.
//!
//! Supported Types
//! ---------------
//! Any type that implements `IntoTemplateVar` can be set as the value of a
//! `UriTemplate` variable. The following implementations are provided by
//! default for each type of variable:
//!
//! - Scalar Values: `String`, `&str`
//! - Lists: `Vec<String>`, `&[String]`, `&[str]`
//! - Associative Arrays: `Vec<(String, String)>`, `&[(String, String)]`,
//!   `&[(&str, &str)]`, `&HashMap<String, String>`
//!
//! In addition, you can implement `IntoTemplateVar` for your own types. View the
//! documentation for `IntoTemplateVar` for information on how that works.

mod percent_encoding;
mod templatevar;

use crate::percent_encoding::{encode_reserved, encode_unreserved};
use std::collections::HashMap;
use std::str::FromStr;
use thiserror::Error;

/// Errors that can occur while parsing a URI template.
#[derive(Debug, Error, PartialEq, Eq)]
pub enum UriTemplateError {
    #[error("unmatched closing brace at position {0}")]
    UnmatchedClosingBrace(usize),
    #[error("unterminated expression starting at position {0}")]
    UnterminatedExpression(usize),
    #[error("empty expression at position {0}")]
    EmptyExpression(usize),
    #[error("invalid variable name '{0}' in expression")]
    InvalidVariableName(String),
    #[error("invalid prefix length '{0}' for variable '{1}'")]
    InvalidPrefix(String, String),
    #[error("expression parsing failed: {0}")]
    Expression(String),
}

pub use crate::templatevar::{IntoTemplateVar, TemplateVar};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VarSpecType {
    Raw,
    Prefixed(u16),
    Exploded,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct VarSpec {
    name: String,
    var_type: VarSpecType,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Operator {
    Null,
    Plus,
    Dot,
    Slash,
    Semi,
    Question,
    Ampersand,
    Hash,
}

#[derive(Clone)]
enum TemplateComponent {
    Literal(String),
    VarList(Operator, Vec<VarSpec>),
}

/// The main struct that processes and builds URI Templates.
use std::fmt;

#[derive(Clone)]
pub struct UriTemplate {
    /// Original template string provided by the caller.  Retained so that the
    /// template can be displayed exactly as it was written.
    original: String,
    components: Vec<TemplateComponent>,
    vars: HashMap<String, TemplateVar>,
}

fn prefixed(s: &str, prefix: u16) -> String {
    let prefix = prefix as usize;
    if prefix >= s.len() {
        s.to_string()
    } else {
        s[0..prefix].to_string()
    }
}

fn is_valid_varname(name: &str) -> bool {
    if name.is_empty() {
        return false;
    }
    // Variable name may consist of ALPHA / DIGIT / "_" or percent encoded triplets
    // e.g. Some%20Thing
    let bytes = name.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        let b = bytes[i];
        match b {
            b'A'..=b'Z' | b'a'..=b'z' | b'0'..=b'9' | b'_' | b'.' => {
                i += 1;
            }
            b'%' => {
                // Need two hex digits after '%'
                if i + 2 >= bytes.len() {
                    return false;
                }
                let h1 = bytes[i + 1];
                let h2 = bytes[i + 2];
                if !((h1 as char).is_ascii_hexdigit() && (h2 as char).is_ascii_hexdigit()) {
                    return false;
                }
                i += 3;
            }
            _ => return false,
        }
    }
    true
}

fn parse_varlist(varlist_input: &str) -> Result<TemplateComponent, UriTemplateError> {
    if varlist_input.is_empty() {
        return Err(UriTemplateError::EmptyExpression(0));
    }

    let mut varlist = varlist_input.to_string();

    let first_char = varlist.chars().next().unwrap();

    let operator = match first_char {
        '+' => Operator::Plus,
        '.' => Operator::Dot,
        '/' => Operator::Slash,
        ';' => Operator::Semi,
        '?' => Operator::Question,
        '&' => Operator::Ampersand,
        '#' => Operator::Hash,
        _ => Operator::Null,
    };

    if operator != Operator::Null {
        varlist.remove(0);
    }

    if varlist.is_empty() {
        return Err(UriTemplateError::EmptyExpression(0));
    }

    let varspecs = varlist.split(',');
    let mut varspec_list = Vec::new();

    for raw_spec in varspecs {
        if raw_spec.is_empty() {
            return Err(UriTemplateError::Expression("empty varspec".to_string()));
        }

        let mut varspec = raw_spec.to_string();
        let mut var_type = VarSpecType::Raw;

        // Handle explode modifier '*'
        if varspec.ends_with('*') {
            varspec.pop();
            var_type = VarSpecType::Exploded;
        }

        // Handle prefix modifier ':<length>'
        if let Some(idx) = varspec.find(':') {
            if var_type == VarSpecType::Exploded {
                // Both explode and prefix not allowed together
                return Err(UriTemplateError::Expression(format!(
                    "both explode and prefix used in '{raw_spec}'"
                )));
            }

            let (name_part, prefix_part) = varspec.split_at(idx);
            let prefix_str = &prefix_part[1..]; // skip ':'
            if prefix_str.is_empty() {
                return Err(UriTemplateError::InvalidPrefix(
                    prefix_str.to_string(),
                    name_part.to_string(),
                ));
            }
            let prefix_num = u16::from_str(prefix_str).map_err(|_| {
                UriTemplateError::InvalidPrefix(prefix_str.to_string(), name_part.to_string())
            })?;

            varspec_list.push(VarSpec {
                name: name_part.to_string(),
                var_type: VarSpecType::Prefixed(prefix_num),
            });
            continue;
        }

        // Variable name validation
        if !is_valid_varname(&varspec) {
            return Err(UriTemplateError::InvalidVariableName(varspec));
        }

        varspec_list.push(VarSpec {
            name: varspec,
            var_type,
        });
    }

    Ok(TemplateComponent::VarList(operator, varspec_list))
}

fn encode_vec<E>(v: &[String], encoder: E) -> Vec<String>
where
    E: Fn(&str) -> String,
{
    v.iter().map(|s| encoder(s)).collect()
}

impl UriTemplate {
    /// Creates a new URI Template from the given template string.
    ///
    /// Example
    /// -------
    /// ```ignore
    /// let t = UriTemplate::new("http://example.com/{name}");
    /// ```
    pub fn new(template: &str) -> Result<UriTemplate, UriTemplateError> {
        let mut components = Vec::new();
        let mut buf = String::new();
        let mut in_varlist = false;

        for (idx, ch) in template.chars().enumerate() {
            if in_varlist {
                if ch == '}' {
                    // End of expression
                    if buf.is_empty() {
                        return Err(UriTemplateError::EmptyExpression(idx));
                    }
                    let var_component = parse_varlist(&buf)?;
                    components.push(var_component);
                    buf.clear();
                    in_varlist = false;
                } else if ch == '{' {
                    // Nested opening brace not allowed
                    return Err(UriTemplateError::UnmatchedClosingBrace(idx));
                } else {
                    buf.push(ch);
                }
            } else if ch == '{' {
                // start expression
                if !buf.is_empty() {
                    components.push(TemplateComponent::Literal(buf.clone()));
                    buf.clear();
                }
                in_varlist = true;
            } else if ch == '}' {
                // unmatched closing brace
                return Err(UriTemplateError::UnmatchedClosingBrace(idx));
            } else {
                buf.push(ch);
            }
        }

        if in_varlist {
            return Err(UriTemplateError::UnterminatedExpression(template.len()));
        }

        if !buf.is_empty() {
            components.push(TemplateComponent::Literal(buf));
        }

        Ok(UriTemplate {
            original: template.to_string(),
            components,
            vars: HashMap::new(),
        })
    }

    /// Sets the value of a variable in the URI Template.
    ///
    /// Example
    /// -------
    /// ```ignore
    /// let mut t = UriTemplate::new("{name}");
    /// t.set("name", "John Smith");
    /// ```
    ///
    /// This function returns the `URITemplate` so that the `set()` calls can
    /// be chained before building.
    ///
    /// ```ignore
    /// let uri = UriTemplate::new("{firstname}/{lastname}")
    ///     .set("firstname", "John")
    ///     .set("lastname", "Smith")
    ///     .build();
    /// assert_eq!(uri, "John/Smith");
    /// ```
    pub fn set<I: IntoTemplateVar>(&mut self, varname: &str, var: I) -> &mut UriTemplate {
        self.vars
            .insert(varname.to_string(), var.into_template_var());
        self
    }

    /// Deletes the value of a variable in the URI Template. Returns `true` if
    /// the variable existed and `false` otherwise.
    ///
    /// Example
    ///
    /// ```ignore
    /// let mut t = UriTemplate::new("{animal}");
    /// t.set("animal", "dog");
    /// assert_eq!(t.delete("house"), false);
    /// assert_eq!(t.delete("animal"), true);
    /// ```
    pub fn delete(&mut self, varname: &str) -> bool {
        self.vars.remove(varname).is_some()
    }

    /// Deletes the values of all variables currently set in the `URITemplate`.
    pub fn delete_all(&mut self) {
        self.vars.clear();
    }

    /// Normalizes the template in-place by lexically sorting all query
    /// parameters (variables that appear in `?` and `&` expressions) and
    /// removing duplicate occurrences.  The *first* occurrence of a variable
    /// is kept while any subsequent duplicates are discarded.  The function
    /// returns a mutable reference to the template so that it can be chained
    /// with other builder-style calls.
    ///
    /// Only the internal representation (`components`) is modified; the
    /// variable assignments that may already have been applied with `set()`
    /// are left untouched.  The `original` template string is also updated so
    /// that `Display` continues to reflect the current representation.
    ///
    /// Example
    /// -------
    /// ```ignore
    /// let mut t = UriTemplate::new("{?b,a}{&b,c}").unwrap();
    /// t.normalize();
    /// assert_eq!(t.to_string(), "{?a,b,c}");
    /// ```
    pub fn normalize(&mut self) -> &mut Self {
        use std::collections::HashSet;

        // First, collect all query-related variables and remember the index of
        // the first query component so that we can re-insert the normalized
        // list in the same position.
        let mut seen: HashSet<String> = HashSet::new();
        let mut query_vars: Vec<VarSpec> = Vec::new();
        let mut first_query_index: Option<usize> = None;
        let mut first_query_operator: Option<Operator> = None;

        for (idx, component) in self.components.iter().enumerate() {
            if let TemplateComponent::VarList(op, vars) = component {
                if *op == Operator::Question || *op == Operator::Ampersand {
                    if first_query_index.is_none() {
                        first_query_index = Some(idx);
                        first_query_operator = Some(op.clone());
                    }

                    for v in vars {
                        if seen.insert(v.name.clone()) {
                            query_vars.push(v.clone());
                        }
                    }
                }
            }
        }

        // Sort the combined query parameters lexicographically by name.
        query_vars.sort_by(|a, b| a.name.cmp(&b.name));

        // Rebuild the components vector.
        let mut new_components: Vec<TemplateComponent> = Vec::with_capacity(self.components.len());

        for (idx, component) in self.components.iter().enumerate() {
            if Some(idx) == first_query_index {
                // Insert the (single) normalized query varlist *once* before
                // processing (and skipping) the existing query components.
                if !query_vars.is_empty() {
                    let op_to_use = first_query_operator.clone().unwrap_or(Operator::Question);
                    new_components.push(TemplateComponent::VarList(op_to_use, query_vars.clone()));
                }
            }

            match component {
                TemplateComponent::VarList(op, _vars)
                    if (*op == Operator::Question || *op == Operator::Ampersand) =>
                {
                    // Skip original query varlists – they've been replaced.
                }
                other => new_components.push(other.clone()),
            }
        }

        // Edge-case: template had query components but they have been removed
        // (e.g., all were duplicates) – ensure we still inserted once.
        if first_query_index.is_some() && query_vars.is_empty() {
            // No query variables – nothing to insert, that's fine.
        }

        // If there were no query components at all just leave the components
        // unchanged (normal case is covered by new_components being empty in
        // that scenario).
        if first_query_index.is_none() {
            // Nothing to normalize
            return self;
        }

        self.components = new_components;

        // Rebuild the textual template so that Display/Debug remain accurate.
        self.original = self.rebuild_template_string();

        self
    }

    /// Helper: constructs a template string from the current `components`
    /// collection.
    fn rebuild_template_string(&self) -> String {
        fn operator_to_char(op: &Operator) -> &'static str {
            match op {
                Operator::Null => "",
                Operator::Plus => "+",
                Operator::Dot => ".",
                Operator::Slash => "/",
                Operator::Semi => ";",
                Operator::Question => "?",
                Operator::Ampersand => "&",
                Operator::Hash => "#",
            }
        }

        let mut out = String::new();

        for component in &self.components {
            match component {
                TemplateComponent::Literal(s) => out.push_str(s),
                TemplateComponent::VarList(op, vars) => {
                    out.push('{');
                    out.push_str(operator_to_char(op));

                    let mut first = true;
                    for v in vars {
                        if !first {
                            out.push(',');
                        }
                        first = false;

                        out.push_str(&v.name);
                        match v.var_type {
                            VarSpecType::Raw => {}
                            VarSpecType::Exploded => {
                                out.push('*');
                            }
                            VarSpecType::Prefixed(p) => {
                                out.push(':');
                                out.push_str(&p.to_string());
                            }
                        }
                    }

                    out.push('}');
                }
            }
        }

        out
    }

    fn build_varspec<E>(
        &self,
        v: &VarSpec,
        sep: &str,
        named: bool,
        ifemp: &str,
        encoder: E,
    ) -> Option<String>
    where
        E: Fn(&str) -> String,
    {
        let mut res = String::new();

        let var = self.vars.get(&v.name)?;

        match *var {
            TemplateVar::Scalar(ref s) => {
                if named {
                    res.push_str(&encode_reserved(&v.name));
                    if s.is_empty() {
                        res.push_str(ifemp);
                        return Some(res);
                    }
                    res.push('=');
                }
                match v.var_type {
                    VarSpecType::Raw | VarSpecType::Exploded => {
                        res.push_str(&encoder(s));
                    }
                    VarSpecType::Prefixed(p) => {
                        res.push_str(&encoder(&prefixed(s, p)));
                    }
                };
            }
            TemplateVar::List(ref l) => {
                if l.is_empty() {
                    return None;
                }
                match v.var_type {
                    VarSpecType::Raw | VarSpecType::Prefixed(_) => {
                        if named {
                            res.push_str(&encode_reserved(&v.name));
                            if l.join("").is_empty() {
                                res.push_str(ifemp);
                                return Some(res);
                            }
                            res.push('=');
                        }
                        res.push_str(&encode_vec(l, encoder).join(","));
                    }
                    VarSpecType::Exploded => {
                        if named {
                            let pairs: Vec<String> = l
                                .iter()
                                .map(|x| {
                                    let val: String = if x.is_empty() {
                                        format!("{}{}", &encode_reserved(&v.name), ifemp)
                                    } else {
                                        format!("{}={}", &encode_reserved(&v.name), &encoder(x))
                                    };
                                    val
                                })
                                .collect();
                            res.push_str(&pairs.join(sep));
                        } else {
                            res.push_str(&encode_vec(l, encoder).join(sep));
                        }
                    }
                }
            }
            TemplateVar::AssociativeArray(ref a) => {
                if a.is_empty() {
                    return None;
                }
                match v.var_type {
                    VarSpecType::Raw | VarSpecType::Prefixed(_) => {
                        if named {
                            res.push_str(&encode_reserved(&v.name));
                            res.push('=');
                        }
                        let pairs: Vec<String> = a
                            .iter()
                            .map(|(k, v)| format!("{},{}", &encode_reserved(k), &encoder(v)))
                            .collect();
                        res.push_str(&pairs.join(","));
                    }
                    VarSpecType::Exploded => {
                        if named {
                            let pairs: Vec<String> = a
                                .iter()
                                .map(|(k, v)| {
                                    let val: String = if v.is_empty() {
                                        format!("{}{}", &encode_reserved(k), ifemp)
                                    } else {
                                        format!("{}={}", &encode_reserved(k), &encoder(v))
                                    };
                                    val
                                })
                                .collect();
                            res.push_str(&pairs.join(sep));
                        } else {
                            let pairs: Vec<String> = a
                                .iter()
                                .map(|(k, v)| format!("{}={}", &encode_reserved(k), &encoder(v)))
                                .collect();
                            res.push_str(&pairs.join(sep));
                        }
                    }
                }
            }
        }

        Some(res)
    }

    fn build_varlist(&self, operator: &Operator, varlist: &Vec<VarSpec>) -> String {
        let mut values: Vec<String> = Vec::new();
        let (first, sep, named, ifemp, allow_reserved) = match *operator {
            Operator::Null => ("", ",", false, "", false),
            Operator::Plus => ("", ",", false, "", true),
            Operator::Dot => (".", ".", false, "", false),
            Operator::Slash => ("/", "/", false, "", false),
            Operator::Semi => (";", ";", true, "", false),
            Operator::Question => ("?", "&", true, "=", false),
            Operator::Ampersand => ("&", "&", true, "=", false),
            Operator::Hash => ("#", ",", false, "", true),
        };

        for varspec in varlist {
            let built = if allow_reserved {
                self.build_varspec(varspec, sep, named, ifemp, encode_reserved)
            } else {
                self.build_varspec(varspec, sep, named, ifemp, encode_unreserved)
            };
            if let Some(s) = built {
                values.push(s)
            }
        }

        let mut res = String::new();
        if !values.is_empty() {
            res.push_str(first);
            res.push_str(&values.join(sep));
        }

        res
    }

    /// Expands the template using the set variable values and returns the
    /// final String.
    ///
    /// Example
    /// -------
    ///
    /// ```ignore
    /// let mut t = UriTemplate::new("{hello}");
    /// t.set("hello", "Hello World!");
    /// assert_eq!(t.build(), "Hello%20World%21");
    /// ```
    pub fn build(&self) -> String {
        let mut res = String::new();
        for component in &self.components {
            let next = match *component {
                TemplateComponent::Literal(ref s) => encode_reserved(s),
                TemplateComponent::VarList(ref op, ref varlist) => self.build_varlist(op, varlist),
            };
            res.push_str(&next);
        }
        res
    }

    /// Returns a map describing all variables that appear in the template
    /// string, keyed by their name.  Each entry contains the `VarSpecType`
    /// (`Raw`, `Prefixed`, or `Exploded`) that was specified for that
    /// variable.
    ///
    /// Because the internal representation is rebuilt on each call, the
    /// returned `HashMap` is owned by the caller; subsequent modifications to
    /// the template have no effect on a previously obtained map.
    pub fn variable_specs(&self) -> HashMap<String, VarSpecType> {
        let mut map = HashMap::new();
        for component in &self.components {
            if let TemplateComponent::VarList(_, ref vars) = component {
                for v in vars {
                    map.entry(v.name.clone())
                        .or_insert_with(|| v.var_type.clone());
                }
            }
        }
        map
    }
}

// --- Trait implementations --------------------------------------------------

impl fmt::Display for UriTemplate {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.original)
    }
}

impl fmt::Debug for UriTemplate {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("UriTemplate")
            .field("template", &self.original)
            .finish()
    }
}

// --- Convenience helper methods on `Result<UriTemplate, UriTemplateError>` ---

// Helper methods for working with `Result<UriTemplate, UriTemplateError>` in
// test code without scattering `unwrap()` calls everywhere.
pub trait UriTemplateResultExt: Sized {
    fn set<I: IntoTemplateVar>(self, varname: &str, var: I) -> Self;
    fn delete(self, varname: &str) -> (Self, bool);
    fn delete_all(self) -> Self;
    fn build(self) -> Result<String, UriTemplateError>;
}

impl UriTemplateResultExt for Result<UriTemplate, UriTemplateError> {
    fn set<I: IntoTemplateVar>(self, varname: &str, var: I) -> Self {
        self.map(|mut t| {
            t.set(varname, var);
            t
        })
    }

    fn delete(self, varname: &str) -> (Self, bool) {
        match self {
            Ok(mut t) => {
                let res = t.delete(varname);
                (Ok(t), res)
            }
            Err(e) => (Err(e), false),
        }
    }

    fn delete_all(self) -> Self {
        self.map(|mut t| {
            t.delete_all();
            t
        })
    }

    fn build(self) -> Result<String, UriTemplateError> {
        self.map(|t| t.build())
    }
}
