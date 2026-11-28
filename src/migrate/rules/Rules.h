// The migration rules, one function per rule (src/migrate/Migrate.h). A
// change that breaks source adds its rule here and to `rules()` in
// Migrate.cpp, with a test in tests/migrate.

#ifndef PIA_MIGRATE_RULES_RULES_H
#define PIA_MIGRATE_RULES_RULES_H

#include "migrate/Migrate.h"

namespace pia::migrate {

// ADR 0064: `let n = type e` made an alias of `e` and now makes a new type.
Rule typeMakesDistinct();

} // namespace pia::migrate

#endif // PIA_MIGRATE_RULES_RULES_H
