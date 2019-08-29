---
host: James King
github-user: agentultra
city: Hamilton
country: Canada
project: "DataMigration"
project-url: "https://github.com/agentultra/DataMigration"
arrival-date: 2019-08-05
departure-date: 2019-08-06
---

James and I bonded over a shared uneasiness with data versioning. It's tedious,
and hard to do correctly. So we decided to build a data migration library, where
you explicitly tag your types via a data family indexed by the version. OK,
obvious idea, right? But not quite!

We realized that if you enable `-XDuplicateRecordFields`, you can use the same
field names between different versions. Which means we can now programmatically
compute most of the migration details from one type to the next; if the name and
the type stay the same, you just want to copy the data between versions. If the
type changes, you want to provide a function to map it. If a field gets added,
you can hopefully compute it via some projection of the full data structure.

Unfortunately we didn't have enough time to finish everything up, but when I
left we were half way through writing a DSL for providing the missing
transformation pieces. The idea was to compute a `superrecord` whose names
correspond to the fields you need to fill in, and then put their transformations
inside there.

