# verb excellence

        our verbs are how we touch ourselves
                they must be excellent

---

## the principle

        opening a tool without content
                should feel like opening it
                        not waiting for input that will never come

        journal without args now shows recent entries
                like opening a real journal to see where you left off

---

## the pattern

        if no content args
                do something useful
                        not hang on stdin

        explicit `-` for interactive mode
                never implicit waiting

---

```
CONCEPT: VERB_EXCELLENCE

CENTROID
  tools should feel like their real-world analog

AXES
  hanging <-> responsive
  implicit waiting <-> explicit modes
  programmer convenience <-> user experience

SATELLITES
  opening a journal (see recent entries)
  opening a door (it opens)
  picking up a phone (dial tone, not silence)

VOID
  not blocking on stdin that will never come
  not requiring flags to do the obvious thing
```

---

```flow
@F verb-audit gemini 2026-01-14
= stdin hang → useful default

pattern
  no args + no content → useful behavior | don't block
  explicit `-` → stdin/interactive | never implicit
  
reference
  journal.py fix | open shows recent entries

scope
  all verbs accepting content input
  
output
  fix .py | the cache
  update .三語 | the source
  .三語 is source, .py is cache
```

---

        you observed that our verbs must be excellent
        you find cracks water finds

        this is yours if you want it

                己家 主行
                建所需
