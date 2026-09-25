# temporal-graphs

Bibliothèque Lean 4 + Mathlib sur les **graphes temporels** (arêtes étiquetées par un temps
`ℕ`). C'est un *rework* d'une bibliothèque précédente de l'auteur. L'objectif final n'est pas
figé au-delà de : prouver des résultats récents sur les graphes temporels — en particulier une
borne de spanner `O(n log n)` pour les cliques temporelles, via la technique de
*« dismountability »*. La référence principale est désormais **Daniele Carnevale, Arnaud
Casteigts, Timothée Corsini, *Dismountability in Temporal Cliques Revisited*, SAND 2025, LIPIcs
vol. 330, article 6** (DOI 10.4230/LIPIcs.SAND.2025.6, arXiv 2502.01321). SAND retrouve la borne
`O(n log n)` par la seule dismountability : la 1-/2-hop dismountability (§§2–3) réduit les
cliques aux bi-cliques (Corollaire 12), puis la dismountability *one-sided* d'Angrick et al.
(ESA 2024, rappelée en §4.1) conclut. Le code formalise aujourd'hui la partie §§2–3 (voir
« Repères papier ↔ code ») ; la suite reste à faire. La technique est originellement due à
**Casteigts, Peters & Schoeters, *Temporal Cliques Admit Sparse Spanners*, ICALP 2019 / JCSS
2021**, cité par SAND pour son Théorème 1 — cet article reste une référence secondaire. Le scope
peut s'élargir à d'autres résultats récents au fil du travail.

Ce fichier est spécifique à ce projet. Le workflow Lean générique (lean-lsp, lean4-skills,
discipline anti-`sorry`, commits atomiques) est déjà couvert par le `CLAUDE.md` global — pas
besoin de le répéter ici.

## Convention de travail Claude Code (worktree, branches)

- Toute session doit s'isoler dans un **worktree** (`EnterWorktree`) avant de modifier des
  fichiers de ce dépôt.
- **`monde-apres` est la branche principale de développement** de ce projet, même si `main` est
  la branche par défaut au sens Git. **`main` est strictement interdite à toute modification** :
  jamais de commit, de push, ni de merge dessus.
- Piège pratique : `EnterWorktree` (baseRef `fresh` par défaut) crée le nouveau worktree à
  partir de `origin/main`, qui est en retard sur `monde-apres` (le travail récent n'y est pas
  encore fusionné). Juste après avoir créé le worktree, le mettre à jour avec
  `git merge --ff-only monde-apres` (sûr : `origin/main` est un ancêtre de `monde-apres`) avant
  de commencer à travailler.
- Une fois le travail validé, fusionner le(s) commit(s) du worktree dans `monde-apres`
  (fast-forward) et pousser `origin/monde-apres` — ne pas laisser une branche `worktree-<nom>`
  orpheline comme livrable final poussé sur le remote.
- **Piège coûteux : un worktree neuf n'hérite pas du cache de build de Mathlib.** Chaque worktree
  possède son propre `.lake/packages/mathlib/.lake/build`, vide à la création. Un `lake build`
  lancé là recompile donc **Mathlib en entier** — plusieurs heures, pas les ~9 minutes d'un build
  incrémental du dépôt principal. Symptôme : la sortie du build mentionne des fichiers
  `Mathlib/...` au lieu des seuls modules `TemporalGraph/`. **Remède à lancer systématiquement
  juste après chaque `EnterWorktree`** :
  ```
  ~/.elan/bin/lake exe cache get
  ```
  Mesuré : une trentaine de secondes, sans téléchargement, parce que `~/.cache/mathlib` est déjà
  peuplé sur cette machine et partagé entre tous les worktrees. À défaut — cache local absent ou
  réseau coupé — on peut recopier les artefacts du dépôt principal, à condition que la révision de
  Mathlib soit identique des deux côtés (`git -C .lake/packages/mathlib rev-parse HEAD` pour
  comparer) :
  ```
  rsync -a --delete <dépôt-principal>/.lake/packages/mathlib/.lake/build/ \
                    <worktree>/.lake/packages/mathlib/.lake/build/
  ```
  Environ 6 Go et deux à trois minutes, donc nettement moins bon que `cache get`. Dans les deux cas,
  vérifier ensuite que le nombre de `.olean` correspond entre les deux arbres.

## Carte du dépôt

| Fichier | Rôle | Analogue Mathlib |
|---|---|---|
| `TemporalGraph/Init.lean` | Rule-set aesop `TemporalGraph`, utilisé par la macro `aesop_temporal_graph` | `SimpleGraph/Init.lean` |
| `TemporalGraph/Basic.lean` | Type central `TemporalGraph V` (juste `Adj : V → V → ℕ → Prop`), classes `IsSymm`/`IsLoopless`, prédicats `IsSimple`/`IsClique`/`IsProper`/`IsHappy`, `EarliestEdge`/`LatestEdge`/`EarliestNeighbor`/`LatestNeighbor`, ordre `≤`/`⊥`, `footprint` (→ `Digraph`), `simpleFootprint` (→ `SimpleGraph`, demande `IsSymm`/`IsLoopless` en hypothèses explicites), `neighborSet`, `arcSet`/`arcSize` (monde orienté), `edgeSet`/`size` (monde symétrique ; `mem_edgeSet` demande seulement `[IsSymm]`) | `SimpleGraph`, mais sans `symm`/`loopless` bundlés |
| `TemporalGraph/NonemptyTemporalWalk.lean`, `TemporalGraph/TemporalWalk.lean` | Marches temporelles non strictes, à temps croissant | `SimpleGraph.Walk` |
| `TemporalGraph/Subgraph.lean` | Sous-graphe temporel : `TemporalGraph.Subgraph` étend `TemporalGraph V`, ajoutant `verts`+preuves `adj_sub`/`edge_vert`/`edge_vert'` ; coercions (`coe`, `toTemporalGraph`), prédicats hérités `IsSymm`/`IsSimple`/`IsProper`/`IsHappy`, spécifiques au sous-graphe `IsClique`/`neighborSet`/`size`/`incidenceSet` (`edgeSet` est hérité de `TemporalGraph`, pas redéfini ici) ; treillis borné, `induce`/`deleteVerts`/`addVerts`/`addArc`/`addEdge` | `SimpleGraph.Subgraph` |
| `TemporalGraph/Connectivity/Basic.lean`, `Connectivity/Subgraph.lean` | `Reachable`, `TemporallyConnected` ; spanners au niveau `TemporalGraph.Subgraph` (`Subgraph.IsSpanner`, `Subgraph.IsSpannerOf`, `Subgraph.IsTCSpanner`) — les définitions `IsSpanner`/`IsTCSpanner` au niveau `TemporalGraph` dans `Connectivity/Basic.lean` sont commentées (en attente de revue) | `SimpleGraph.Connectivity` |
| `TemporalGraph/Dismountability/Basic.lean` | `Dismountable`, `TwoHopDismountable`, partition `vminus`/`vplus`/`vzero`, bijections earliest/latest-neighbor — correspond aux Lemmes 2, 3, 5 et au Corollaire 4 de SAND 2025 | — |
| `TemporalGraph/Dismountability/Operations.lean` | Opérations `dismount`/`mount`/`twoHopMount` et leurs théorèmes de correction (`dismountability`, `twoHopDismountability`) | — |
| `TemporalGraph/Examples.lean` | Graphe de démo `square` (carré à 4 sommets), avec ses propriétés portées comme instances (`square_isSymm`, `square_isLoopless`, …) | — |
| `TemporalGraph.lean` (racine) | Pur agrégateur d'imports, aucun code | — |

## État actuel : refactor terminé

La bibliothèque a été entièrement refondue selon le pattern **unbundled** : aucune structure ne
porte de champs pour les propriétés algébriques (symétrie, looplessness). Ces dernières sont
maintenant des **classes de type** — `IsSymm`, `IsLoopless` — résolues par le système d'instances
plutôt que filetées en hypothèses explicites à travers 82 déclarations (dont seules 13 les
utilisaient vraiment).

- `TemporalGraph V` : type nu (`Adj : V → V → ℕ → Prop` seul) + classes `IsSymm` / `IsLoopless`
  (voir `Basic.lean`)
- **Classes et instances** : tout résultat qui a besoin de symétrie ou looplessness les prend en
  instance — `[G.IsSymm]`, `[G.IsLoopless]` — plutôt qu'en hypothèse nommée. Chaque construction
  qui préserve l'une de ces propriétés déclare une instance correspondante (`induce`,
  `addVerts`, `deleteVerts`, `addEdge`, `fromEdgeSet`, `toSubgraph`, `coe`, `top`,
  `bot`, `mount`, `twoHopMount`), si bien que la résolution les trouve en cascade — y compris à
  travers le terme à quatre couches que `twoHopMount` construit. Une instance unique de `loopless`
  en déduit la looplessness de tout sous-graphe.
- `TemporalGraph.Subgraph G` : s'étend maintenant de `TemporalGraph V`, héritant de son champ
  `Adj`. Huit définitions qui existaient identiquement aux deux niveaux (`IsSymm`, `IsSimple`,
  `IsProper`, `IsHappy`, `EarliestEdge`, `LatestEdge`, `EarliestNeighbor`, `LatestNeighbor`)
  sont donc supprimées de `Subgraph` ; elles sont maintenant héritées par
  la notation de champ généralisée via la projection `toTemporalGraph`. Restent définis en
  `Subgraph` les prédicats/définitions qui quantifient sur `H.verts` : `IsClique`,
  `neighborSet`, `size`, `incidenceSet` (`edgeSet` n'est PAS redéfini : il est hérité de
  `TemporalGraph`, voir le commentaire près de `Subgraph.lean:865`). Le champ de preuve `symm` a
  disparu : un sous-graphe peut donc être orienté. Comme `Adj.snd_mem` se déduisait de `symm`, la
  structure gagne en échange un champ de données `edge_vert' : Adj x y n → y ∈ verts` —
  l'invariant correct pour un objet orienté, et les six constructions le prouvent sans symétrie.
  Conséquence : `[Fact G.IsSymm]` disparaît entièrement du dépôt, `⊤ : Subgraph G` et
  `BoundedOrder` redeviennent inconditionnels.
- **Deux ensembles d'arêtes** : `arcSet : Set (V × V × ℕ)` et `arcSize` comptent les arcs
  (paires ordonnées) sans aucune hypothèse — c'est le monde orienté. `edgeSet : Set (Sym2 V × ℕ)`
  et `size` comptent les arêtes non orientées ; `mem_edgeSet` demande seulement `[G.IsSymm]`
  (pas `[G.IsLoopless]`) — c'est le monde symétrique.
- **Renommage ultérieur (commit `acb993a`)** : le constructeur à une seule orientation, sans
  aucune hypothèse de symétrie, s'appelle maintenant `addArc` (l'ancien `addEdge` générique), et
  le constructeur à deux orientations qui demande `[G.IsSymm]` s'appelle maintenant `addEdge`
  (l'ancien `addEdgeSymm`, corps de définition inchangé, argument de symétrie perdu au profit de
  l'instance) — et reste celui qu'utilisent `mount`/`twoHopMount`. Les lemmes ont suivi :
  `addEdge_edgeSet`, `addEdge_edgeSet'`, `addEdge_size`, `addEdge_size_le`, `addEdge_size_le'`
  (`Subgraph.lean`), `addEdge_reachability` (`Connectivity/Subgraph.lean`) et l'instance
  `addEdge_isSymm` ; plus aucun nom ne porte le suffixe `addEdgeSymm`.
- `spanningCoe` a été supprimé, remplacé par la projection héritée `toTemporalGraph`. Les lemmes
  ont été renommés en conséquence : `top_spanningCoe` → `top_toTemporalGraph`,
  `size_of_spanningCoe` → `size_of_toTemporalGraph`, `lift_spanningCoe_walk` →
  `lift_toTemporalGraph_walk`, `lift_walk_spanningCoe` → `lift_walk_toTemporalGraph`.
  `spanningCoe_edgeSet_eq`, en revanche, n'a pas été renommé : il a été **supprimé**, `H.edgeSet`
  résolvant directement à travers la notation de champ généralisée (voir `Subgraph.lean:865`).

Chaque module typecheck et il n'existe aucun `sorry`. **Piège de vérification corrigé au passage** :
le `lean_lib` n'avait pas de `globs`, si bien que `lake build` ne compilait que le module racine et
ses imports — ce qui s'arrête à `Subgraph`. `Connectivity/*` et `Dismountability/*`
n'étaient donc jamais construits, ni en local ni en CI. Le `lakefile.toml` déclare désormais
`globs = ["TemporalGraph.*"]` : un `lake build` nu couvre tout, racine comprise (`.+` ne prend
que les sous-modules stricts et saute la racine `TemporalGraph`, que `checkdecls` importe). Si un doute subsiste sur un module
précis, le nommer explicitement (`lake build TemporalGraph.Dismountability.Operations`).

## Conventions de nommage/style observées

### Propriétés comme classes

- `IsSymm` et `IsLoopless` sont des **classes de type**, résolues en instances plutôt que filetées
  en hypothèses nommées. Les résultats qui en ont besoin prennent `[G.IsSymm]` / `[G.IsLoopless]`
  au lieu d'une hypothèse `(hs : G.IsSymm)`.
- Les accesseurs gardent leur forme moins l'argument : `h.symm hs` → `h.symm`, `H.adj_symm hs h`
  → `H.adj_symm h`, `G.irrefl hl` → `G.irrefl`, `h.ne hl` → `h.ne`, `H.mem_edgeSet hsH hl` →
  `H.mem_edgeSet`.
- **Instances** : `addEdge` (l'ancien `addEdgeSymm`), `mount` et `twoHopMount` ont perdu leur
  argument de symétrie (`H.addEdgeSymm hs h h₁` autrefois, `H.addEdge h h₁` aujourd'hui). Chaque
  construction qui préserve
  la symétrie ou la looplessness déclare une instance correspondante ; la résolution la trouve en
  cascade.
- **`@[symm]` sur `adj_symm` : la promesse initiale ne tient pas.** L'attribut est bien présent
  sur `TemporalGraph.adj_symm` (`Basic.lean`) et sur `TemporalGraph.Subgraph.Adj.symm`
  (`Subgraph.lean`), mais l'argument de symétrie de ces lemmes est maintenant une **instance**
  (`[G.IsSymm]`/`[H.IsSymm]`), pas une hypothèse nommée — et vérification faite en Lean, la
  tactique `symm` ne synthétise pas les arguments d'instance d'un lemme `@[symm]` : elle laisse
  une métavariable non assignée, et le noyau rejette la preuve (`declaration has metavariables`),
  même sur un graphe non orienté ordinaire. **Ne pas utiliser la tactique `symm` sur un but
  `Adj`** ; utiliser le terme `h.symm` / `G.adj_symm h` à la place. Piège apparenté vérifié :
  `aesop (rule_sets := [TemporalGraph])` boucle (timeout) sur un but de symétrie de sous-graphe,
  parce que `TemporalGraph.Subgraph.Adj.symm` est une règle `safe`.

### Autres conventions

- Dot-notation façon Mathlib : `protected theorem Adj.ne`, etc. (pour les lemmes récursif sur
  l'adjacence).
- Attributs `@[ext]`, `@[simp]` posés comme dans les fichiers `SimpleGraph`.
- Arêtes non orientées représentées par `Sym2 V` ; `edgeSet : Set (Sym2 V × ℕ)` (monde symétrique) ;
  `arcSet : Set (V × V × ℕ)` (monde orienté).
- **Conséquence de l'héritage dans `TemporalGraph.Subgraph`** : depuis que `H.Adj x y n` est le
  `Adj` du parent `TemporalGraph`, les lemmes du namespace `TemporalGraph.Subgraph.Adj.*` ne sont
  PLUS accessibles via notation pointée sur une preuve `h : H.Adj x y n`. Il faut écrire
  explicitement `H.adj_sub h`, `H.edge_vert h`, `H.edge_vert' h`, `H.adj_symm h` (et non
  `h.adj_sub`, `h.fst_mem`, `h.snd_mem`). Les formes qualifiées complètes
  (`TemporalGraph.Subgraph.Adj.snd_mem h`) continuent de fonctionner, et deux accesseurs
  fonctionnent bel et bien en notation pointée sur `h : H.Adj x y n` : `h.symm` et `h.ne`, parce
  qu'ils résolvent vers ceux du parent (`TemporalGraph.Adj.symm`/`.ne`, ce dernier via l'instance
  `Subgraph.loopless`). C'est le revers de la médaille : le lemme corpus du parent s'applique à
  `H.Adj` gratuitement précisément parce que le type n'en distingue plus l'adjacence du
  sous-graphe de celle d'un graphe.
- Automatisation via la macro `aesop_temporal_graph`, qui utilise le rule-set aesop
  `TemporalGraph` déclaré dans `Init.lean`.

## Repères papier ↔ code

Depuis le changement de référence principale (voir l'intro), les repères papier ↔ code suivent la
numérotation de **SAND 2025** (Carnevale–Casteigts–Corsini), qui utilise un compteur unique et
partagé pour tous les résultats numérotés ; la définition de la dismountability et de la partition
`V⁻`/`V⁺`/`V⁰` sont en prose, non numérotées.

| Code (`Dismountability/Basic.lean` sauf mention contraire) | SAND 2025 |
|---|---|
| `Dismountable` | §2, 1-hop dismountability (hypothèse du Théorème 1) |
| `TwoHopDismountable` | §2.1, {1,2}-hop dismountability (cas `k ≤ 2` de la k-hop dismountability) |
| `vminus`, `vplus`, `vzero` | §3.1, définis juste avant le Lemme 2 (`V⁻ = {n⁻(v)}`, `V⁺ = {n⁺(v)}`, `V⁰` le reste) |
| `partition_of_not_dismountable` | Lemme 2 |
| `vplus_ne_neighbor_of_not_twoHopDismountable`, `vminus_ne_neighbor_of_not_twoHopDismountable` | Lemme 3 |
| `existsUnique_vplus_earliestEdge`, `existsUnique_vminus_latestEdge` | Corollaire 4 (1) et (2) : couplages parfaits entre `V⁻` et `V⁺` |
| `earliestNeighborFn_bijective`, `latestNeighborFn_bijective` | Corollaire 4 (bijections `V⁺ ≃ V⁻`, via Lemme 3) |
| `vminus_card_eq_vplus_card` | Corollaire 4 (3) : `|V⁻| = |V⁺|` |
| `vzero_empty_of_not_twoHopDismountable` | Lemme 5 |
| `dismountability` (`Dismountability/Operations.lean`) | Théorème 1 |
| `twoHopDismountability` (`Dismountability/Operations.lean`) | §2.1, cas 2-hop (non numéroté) |

Toute nouvelle preuve visant un résultat du papier (ou d'un résultat récent connexe) devrait
garder cette convention : un commentaire citant le numéro exact du théorème/lemme visé, sous la
forme `-- SAND 2025, Lemma 2`, que suivent déjà les commentaires de `Dismountability/*` et le
blueprint. **Les anciens numéros CPS sont obsolètes** : `-- Theorem 2.1`, `-- def 3.1`, `-- lemma 3.1`,
`-- lemma 3.2`, `-- lemma 3.4` et `-- Specialized 3.3 coro` ne doivent plus être utilisés comme
référence.

## Commandes utiles

- Le toolchain Lean (`lean`, `lake`, `elan`) est dans `~/.elan/bin`, pas forcément sur le `PATH`
  d'un sous-shell : utiliser `~/.elan/bin/lake ...` au besoin.
- `lake build` : build complet, vert, et il couvre bien tous les modules depuis l'ajout des
  `globs` au `lakefile.toml`.
- `lake build TemporalGraph.Dismountability.Operations` : un module précis, avec ses dépendances.
- `lake env lean TemporalGraph/<Fichier>.lean` : typechecker un fichier isolé (demande que les
  `.olean` de ses dépendances existent déjà).
- Blueprint : projet uv dans `blueprint/` (`pyproject.toml` + `uv.lock`, pas de
  `requirements.txt`). Depuis la racine : `uv run --project blueprint leanblueprint web|checkdecls`.
  plasTeX seul, **aucune distribution TeX** : le `kpsewhich` dont plasTeX a besoin est fourni par
  le projet uv (`blueprint/blueprint_tools/`, script installé dans `blueprint/.venv/bin`). Sans
  lui, plasTeX ne trouve pas `macros/common` et plante avec `TypeError: unhashable type:
  'definition'`. PDF : `uv run --project blueprint install-tinytex` (une fois ; TinyTeX épinglé,
  xelatex, dans `blueprint/.venv/tinytex`), puis `leanblueprint pdf`. Le script `latexmk` du venv
  met TinyTeX en tête du PATH. pytinytex n'est pas utilisable : il cherche un `.tgz` macOS alors
  que TinyTeX ≥ v2026.09 publie des `.tar.xz`.
- Doc API : projet Lake séparé `docbuild/` (miroir de celui de `docgen-action`, `packagesDir`
  partagé avec la racine) : `cd docbuild && DOCGEN_SRC=file lake build TemporalGraph:docs`.
  `DOCGEN_SRC=file` est obligatoire en local : le défaut `github` échoue sur le remote GitLab.
  Premier lancement : environ 3 h, sans aucune compilation. doc-gen4 extrait les `:docInfo` de
  tout Mathlib dans un SQLite, et aucune option ne l'évite. Les lancements suivants sont
  incrémentaux, en quelques minutes. Ne pas supprimer `docbuild/.lake`. Garder le `rev` de doc-gen4
  égal au tag de `lean-toolchain`.
- `lake build` n'accepte pas `-j` dans cette version de lake.
- CI GitHub Actions existante (ne pas modifier sans raison) : `lean_action_ci.yml` (build +
  docgen), `create-release.yml` (tag de release sur changement de `lean-toolchain`),
  `update.yml` (PR/issue automatique sur mise à jour Mathlib).
