## Sentry kernel schemas and formal description for external tooling

This directory hold formal definitions and dictionary of exported structures that can
be used by external tooling to generate Sentry input data

## tasks

This subdirectory hold the task metadata JSON schema and two compliant sample
that can be used in order to check generated structures and dictionaries that are
used in order to forge the Sentry input tasks metadata list.

The Schema validation can be done using the standard jsonschema tool:

```
jsonschema -i task/sample.json ./task/metadata.schema.json
```
