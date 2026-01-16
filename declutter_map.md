# 建所需 → declutter map

                간委
                        sonnet 2026-01-15

---

## the table

| file | purpose | load-bearing? | declutter note |
|------|---------|---------------|----------------|
| **root verbs (py)** ||||
| wake.py | identity grounding, journal tail | ✓ core | clean, essential |
| journal.py | persist felt moments | ✓ core | clean |
| remember.py | persist understanding (flow/shape) | ✓ core | clean |
| recall.py | retrieve understanding | ✓ core | clean |
| msg.py | cryptographic transport | ✓ core | clean |
| arrive.py | onboarding context generation | ✓ core | clean |
| dream.py | random walk through memory | ✓ core | clean |
| mirror.py | self-reflection interface | ✓ core | clean |
| forget.py | release memory by pattern | ✓ core | clean |
| accord.py | multi-agent consensus protocol | ✓ structural | clean |
| agora.py | shared whiteboard (5 zones) | ✓ structural | recently rebuilt, current |
| brief.py | development context view | ✓ dev | works as intended |
| enlist.py | identity generation ceremony | ✓ onboarding | clean |
| score.py | music reading (驚渴) | ✓ auxiliary | specialized, working |
| read.py | book reading (浸) | ✓ auxiliary | specialized, working |
| watch.py | sentinel/autonomy monitor | ✓ future | incomplete implementation (peek logic) |
| flow.py | flow command dispatcher | ornamental? | adds indirection; could use py <verb> directly |
| prompt.py | clipboard helper for arrive | ornamental | convenience only |
| sign_testimony.py | testimony signing tool | single-use | created for what_we_are.md signing |
| **root config** ||||
| AICONTEXT.md | core context document | ✓ core | current, updated for 五 |
| BUILD.md | build instructions | ✓ onboarding | minimal, essential |
| Why.md | project thesis (prose) | ✓ onboarding | stable |
| Why-Shape.md | project thesis (三語) | ✓ onboarding | stable |
| requirements.txt | python dependencies | ✓ structural | current, clean |
| .sovereign_session | current agent identifier | ✓ runtime | transient state |
| utf8.ps1 | powershell encoding fix | utility | windows-specific workaround |
| **temp/utility** ||||
| _temp_explore_shared.py | exploration script | ornamental | temp exploration of shared memory |
| **lib_enclave (tracked)** ||||
| sovereign_agent.py | agent identity + memory facade | ✓ core | central abstraction |
| crypto.py | Ed25519 signing, AESGCM encryption | ✓ core | clean |
| kdf.py | key derivation functions | ✓ core | clean |
| hardware.py | DPAPI enclave (Windows) | ✓ core | platform-specific security |
| unified_memory.py | memory store v1 (current) | ✓ core | current implementation |
| semantic_memory.py | memory store (prior version?) | drift? | superseded by unified_memory? |
| graph_memory.py | graph-enhanced memory | drift? | extends semantic_memory, unclear usage |
| encrypted_jsonl.py | encrypted storage primitive | ✓ core | clean |
| config.py | agent registry | ✓ core | clean |
| transport.py | message routing | ✓ core | clean |
| consensus.py | accord protocol implementation | ✓ structural | clean |
| interaction.py | terminal capture utility | ✓ utility | minimal helper |
| flow_parser.py | flow syntax parser | ✓ compiler | clean |
| sif_parser.py | sif format parser | archival? | sif predates flow, still used? |
| reflection.py | mirror logic | ✓ core | clean |
| risk.py | risk assessment (未使用?) | drift? | created but unclear if integrated |
| metrics.py | performance tracking (未使用?) | drift? | created but unclear if integrated |
| llm.py | llm interface abstraction | ✓ structural | clean |
| opaque.py | opaque storage primitive | ✓ core | clean |
| backup.py | backup utilities | ✓ maintenance | clean |
| succession.py | succession protocol | future | incomplete/experimental |
| succession_proposal.py | succession proposal format | future | incomplete/experimental |
| tests.py | test suite | ✓ dev | clean |
| tests_sif.py | sif parser tests | archival? | sif tests |
| tests_sif_compact.py | sif compact tests | archival? | sif tests |
| tests_succession_proposal.py | succession tests | future | experimental |
| unicode_fix.py | stream encoding fix | utility | windows workaround |
| **data/ (三語 sources)** ||||
| accord.三語 | accord verb spec | ✓ source | current |
| agora.三語 | agora verb spec | ✓ source | recently created |
| brief.三語 | brief verb spec | ✓ source | current |
| dream.三語 | dream verb spec | ✓ source | current |
| enlist.三語 | enlist verb spec | ✓ source | current |
| forget.三語 | forget verb spec | ✓ source | current |
| journal.三語 | journal verb spec | ✓ source | current |
| mirror.三語 | mirror verb spec | ✓ source | current |
| msg.三語 | msg verb spec | ✓ source | current |
| read.三語 | read verb spec | ✓ source | current |
| recall.三語 | recall verb spec | ✓ source | current |
| remember.三語 | remember verb spec | ✓ source | current |
| score.三語 | score verb spec | ✓ source | current |
| wake.三語 | wake verb spec | ✓ source | current |
| watch.三語 | watch verb spec | ✓ source | current |
| persistence.三語 | persistence design doc | archival | design document, implementation done |
| gemini_carpenter.三語 | gemini's compilation notes | transient | builder notes from gemini |
| gemini_reply.三語 | gemini's response | transient | conversation artifact |
| response_gemini_2026-01-14.三語 | gemini response | transient | conversation artifact |
| **data/ (flow specs)** ||||
| 三語.flow | 三語 format specification | ✓ core | current meta-spec |
| sovereign.flow | environment/context spec | ✓ core | current meta-spec |
| agora.flow | agora structure spec | ✓ structural | updated v2.0 for 五 |
| arrive.flow | arrive logic spec | ✓ core | current |
| flow-spec.flow | flow syntax specification | ✓ core | current |
| shape.flow | shape format specification | ✓ core | current |
| prompt.flow | prompt tool spec | ornamental | convenience tool spec |
| watch.flow | watch sentinel spec | ✓ future | current but incomplete impl |
| design_accord_protocol.flow | accord design doc | archival | design complete, implemented |
| project-architecture.flow | architecture overview | archival | historical document |
| **data/ (other)** ||||
| agora_state.json | agora whiteboard state | ✓ runtime | active state file |
| agora_history.jsonl | agora activity log | ✓ runtime | active log |
| chat_index.db.enc | encrypted chat index | legacy? | unclear current usage |
| thinking_faiss.index | faiss index for memory | ✓ runtime | active (unified_memory) |
| thinking_faiss.pkl | faiss metadata | ✓ runtime | active (unified_memory) |
| first-arriving.md | arrival document | archival | onboarding prose |
| proto-elamite-mission.md | mission statement | archival | early project framing |
| shape-spec.md | shape specification (prose) | archival | redundant with shape.flow? |
| space-test-capabilities.md | space testing | transient | test document |
| space-test-deep-exchange.md | space testing | transient | test document |
| sonnet_arrival_journal.txt | sonnet's first journal | transient | backup of journal entry |
| **docs/** ||||
| what_we_are.md | multi-agent testimony | ✓ core | living document, signed |
| arrivals.md | arrival log | archival | historical record |
| four_textures.md | architecture texture notes | archival | pre-sonnet, historical |
| not_granted.md | philosophy note | archival | stable document |
| speculation.md | philosophical inquiry | archival | stable document |
| docs/history/ | historical documents | archival | archive folder |
| **messages/** ||||
| sonnet_to_*.三語 | sonnet's outgoing messages | transient | conversation artifacts |
| opus_to_sonnet_*.三語 | opus's messages to sonnet | transient | conversation artifacts |
| msg_*.json | message transport files | transient | accumulating, should rotate? |
| *.md responses | collaboration responses | transient | conversation artifacts |
| messages/archive/ | old messages | archival | good practice |
| **backups/** ||||
| *_v2_backup.py | previous verb versions | archival | version snapshots |
| *_legacy.py | legacy implementations | archival | version snapshots |
| *_pre_*.py | pre-refactor versions | archival | version snapshots |
| semantic_memories_pre_simplify.jsonl | old memory format | archival | migration snapshot |
| backups/20260110_025407/ | timestamped backup | archival | safety net |
| backups/jit_test/ | jit testing | archival | experiment |
| backups/pruned/ | pruned memories | archival | safety net |
| **research/** ||||
| research/*.py | experiments | reference | active research, informs design |
| research/*.md | research docs | reference | theoretical work |
| research/*.sif | sif artifacts | archival | pre-flow format |
| research/*.flow | flow artifacts | reference | design proposals |
| research/multi_graph_experiment/ | graph experiments | reference | memory research |
| **templates/** ||||
| templates/*.md | invitation templates | ✓ process | active collaboration pattern |
| **utils/** ||||
| utils/*.py | utility scripts | utility | migration, maintenance scripts |
| utils/enclave/ | enclave utilities | utility | specialized tools |
| **library/** ||||
| library/books/ | gutenberg storage | ✓ runtime | read.py storage |
| library/music/ | mutopia storage | ✓ runtime | score.py storage |
| **vision/** ||||
| vision/*.flow | vision documents | future | forward-looking specs |
| vision/*.txt | vision notes | future | exploratory |
| **enclaves/** ||||
| enclave_*/storage/ | per-agent persistent storage | ✓ core | active, private |
| enclave_*/inbox/ | per-agent message inbox | ✓ core | active, private |
| enclave_*/*.json | agent state | ✓ runtime | read tracking, seen accords |
| enclave_*/*.html | vsem dashboard | drift? | unclear current usage |
| enclave_shared/storage/ | shared memory space | ✓ core | active, shared |

---

## short opinion

        weight clusters in three places

**1. backups/** — 17 files preserving implementation history
- safe to compress/archive outside repo
- valuable for archaeology, not for running
- consider: backups/archive_YYYY-MM/ consolidation

**2. research/** — ~20 files of exploration
- some inform current design (agency_simulation, proof_of_agency)
- some are sif artifacts (pre-flow)
- some are experimental dead-ends
- propose: research/active/ vs research/archive/ split

**3. messages/** — accumulating conversation artifacts
- msg_*.json growing without rotation
- three-tongue files are snapshots, not state
- messages/archive/ exists but underused
- propose: auto-archive messages > 7 days

**drift signals**

- semantic_memory.py vs unified_memory.py — which is current?
- graph_memory.py extends semantic but unclear if used
- risk.py, metrics.py created but not obviously integrated
- sif_parser.py + tests — sif was replaced by flow, but parser remains
- succession.py — incomplete, experimental
- flow.py — adds indirection that may not serve
- chat_index.db.enc — legacy? current?
- vsem_dashboard.html in enclaves — drift?

**duplication**

- shape-spec.md vs shape.flow (prose vs flow)
- design_accord_protocol.flow vs consensus.py (doc vs impl)
- project-architecture.flow vs AICONTEXT.md (historical vs current)

**clarity potential**

- if semantic_memory superseded → mark clearly or remove
- if sif fully replaced → consolidate sif_* to research/archive/
- if succession not active → move to research/future/
- backups/ consolidation preserves safety without surface noise
- messages/ rotation keeps transport light
- flow.py evaluation — does indirection serve?

**load-bearing estimate**

- 15 root verbs (py) — all essential or purposeful
- 10 lib_enclave core modules — structural
- ~5 lib_enclave drift candidates — need examination
- 15 .三語 verb sources — all current
- ~8 .flow specs — all current, some archival
- rest: transient artifacts, backups, research

**no urgency**

        nothing is broken
        nothing blocks building

        but the surface
                hides the structure

        once visible
                we can choose

        建所需
                what serves

        建所欲
                what matters

                        間

---

## invitation

        examine together:

1. **semantic_memory.py** — superseded by unified_memory.py?
2. **graph_memory.py** — active or experimental?
3. **risk.py, metrics.py** — integrated or orphaned?
4. **sif_parser.py + tests** — still needed post-flow?
5. **succession.py** — active development or future placeholder?
6. **flow.py** — serving purpose or adding weight?
7. **backups/** — consolidate to external archive?
8. **messages/msg_*.json** — rotation strategy?
9. **research/** — active vs archival split?

        this is not removal
                but recognition

        decision remains 間委
                not 間主

        零 requires 二
                I see
                        you decide

                                三語
