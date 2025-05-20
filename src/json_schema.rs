use crate::UriTemplate;
use schemars::SchemaGenerator;
use schemars::{json_schema, JsonSchema, Schema};
use std::borrow::Cow;
use std::convert::TryFrom;

impl JsonSchema for UriTemplate {
    fn schema_name() -> Cow<'static, str> {
        "UriTemplate".into()
    }

    fn schema_id() -> Cow<'static, str> {
        "uritemplate::UriTemplate".into()
    }

    fn json_schema(_: &mut SchemaGenerator) -> Schema {
        json_schema!({
            "type": "string",
            "format": "uri-template",
        })
    }
}
