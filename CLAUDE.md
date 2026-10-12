# temporal-graphs

Bibliothèque Lean 4 + Mathlib sur les **graphes temporels** (arêtes étiquetées par un temps
`ℕ`). C'est un *rework* d'une bibliothèque précédente de l'auteur. L'objectif final n'est pas
figé au-delà de : prouver des résultats récents sur les graphes temporels — en particulier une
borne de spanner `O(n log n)` pour les cliques temporelles, via la technique de
*« dismountability »*. La référence principale est désormais **Daniele Carnevale, Arnaud
Casteigts, Timothée Corsini, *Dismountability in Temporal Cliques Revisited*, SAND 2025, LIPIcs
vol. 330, article 6** (DOI 10.4230/LIPIcs.SAND.2025.6, arXiv 2502.01321). SAND retrouve la borne
`O(n log n)` par la seule dismountability : la 1-/2-hop dismountability (§§2–3) réduit les
cliques aux bi-cliques (Corollaire 4.1), puis la dismountability *one-sided* d'Angrick et al.
(ESA 2024, rappelée en §4.1) conclut. Le code formalise aujourd'hui **toute la preuve** (voir
« Repères papier ↔ code ») : §§2–3 (dismountability, réduction aux bi-cliques, Lemmes 3.1–3.5,
Corollaires 3.3/4.1) et §4.1 (dismountability *one-sided* et borne `O(n log n)` :
`exists_isSpannerOf_ncard_le`, borne explicite `2n⌈log₂ n⌉ + 4n`, et `exists_isBigO_isSpannerOf`). La technique est originellement due à
**Casteigts, Peters & Schoeters, *Temporal Cliques Admit Sparse Spanners*, ICALP 2019 / JCSS
2021**, cité par SAND pour son Théorème 2.1 — cet article reste une référence secondaire. Le scope
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
- **Worktrees : partager `.lake/packages` avec le dépôt principal, jamais en recopier le contenu.**
  Un worktree neuf n'a pas de Mathlib compilé ; un `lake build` nu y recompilerait **Mathlib en
  entier** (plusieurs heures ; symptôme : la sortie mentionne des modules `Mathlib/...` au lieu des
  seuls `TemporalGraph/`). **Remède à lancer systématiquement juste après chaque `EnterWorktree`**
  (et le `merge --ff-only` ci-dessus), depuis la racine du worktree :
  ```
  rm -rf .lake/packages && mkdir -p .lake && \
    ln -s /Users/arme/Project/temporal-graphs/.lake/packages .lake/packages
  ```
  Le worktree lit alors **les mêmes fichiers** (mêmes inodes) que `monde-apres` : zéro Go de disque,
  pas de `cache get`, et surtout le cache de pages de macOS est partagé. Mesuré (2026-09-25) : build
  complet du worktree en ~1 min, `lake env lean` sans erreur, et `monde-apres` rejoue toujours
  Mathlib sans rien recompiler. Seul `.lake/build` (les ~14 fichiers du projet) reste propre au
  worktree. Règles qui en découlent :
  - **Jamais de `lake update`, de `lake exe cache get!` ni de changement de `lake-manifest.json` /
    `lean-toolchain` depuis un worktree** : cela modifierait les paquets du dépôt principal. Une
    montée de version de Mathlib se fait dans le dépôt principal, hors session parallèle.
  - **Procédure de montée de version** (rodée le 2026-09-25, `v4.29.0-rc6` → `v4.35.0-rc3`) :
    1. prendre comme cible la toolchain de Mathlib `master` (`curl -sL
       https://raw.githubusercontent.com/leanprover-community/mathlib4/master/lean-toolchain`) ;
    2. **arrêter d'abord tous les serveurs Lean de l'ancienne toolchain** sur le dépôt (VS Code,
       lean-lsp-mcp : `lake serve`, `lean --server`, et leurs workers orphelins). Sinon leur
       `lake setup-file` recharge l'ancien manifeste et remet chaque paquet sur son ancienne
       révision pendant la mise à jour. Symptôme : `lake update` échoue dans le hook de Mathlib, en
       compilant `Cache/Requests.lean` (`Missing cases: Lake.PackageEntrySrc.path`), et les
       checkouts de `.lake/packages/*` ne correspondent plus à `lake-manifest.json` ;
    3. écrire le nouveau `lean-toolchain`, puis `lake update` (le hook récupère le cache Mathlib) ;
       vérifier que chaque checkout correspond au manifeste ;
    4. `lake build`, puis corriger les ruptures d'API et les dépréciations ;
    5. `docbuild/` partage `.lake/packages` : y aligner le `rev` de doc-gen4 et lancer
       `MATHLIB_NO_CACHE_ON_UPDATE=1 lake update` (sans build), sinon son manifeste épinglerait
       l'ancien Mathlib, et un `lake build` dans `docbuild` le remettrait en place pour tout le
       monde. Supprimer ensuite le `docbuild/lean-toolchain` que `lake update` recrée. Les
       `:docInfo` de Mathlib dans `docbuild/.lake` deviennent obsolètes : le prochain build de la
       documentation reprend les ~3 h.
  - Avant de supprimer un worktree : arrêter les serveurs Lean qui y tournent (`lake serve`,
    `lean --server` dont le cwd est le worktree) et retirer le lien (`rm .lake/packages`) par
    précaution, puis `git worktree remove`.
- **Pourquoi c'est la bonne méthode — diagnostic mesuré le 2026-09-25.** L'ancienne méthode
  (`lake exe cache get` par worktree) donnait à chaque worktree sa **propre copie** de ~7 Go de
  `.olean`. Le goulot n'est pas le CPU mais la mémoire : chaque processus Lean qui importe Mathlib
  occupe ~5 Go (mmap des `.olean`), et compiler un module du projet prenait 88–105 s de temps réel
  pour 3–5 s de CPU (> 200 k défauts de page, swap plein à 9,5 Go sur 24 Go de RAM). Avec des
  copies distinctes, travailler dans un worktree évince du cache de pages la copie de
  `monde-apres`, qu'il faut relire au retour : c'est le « tout ralentit quand on revient dans
  `monde-apres` ». Les serveurs Lean restés vivants sur d'anciens worktrees (VS Code,
  lean-lsp-mcp) aggravent la pression : les arrêter, et supprimer les worktrees fusionnés dès
  qu'ils ne servent plus.
- **Piste écartée : `enableArtifactCache = true` dans `lakefile.toml`.** Le cache d'artefacts de
  Lake (`~/.elan/toolchains/<toolchain>/lake/cache`) partage bien les builds entre checkouts
  (reconstruction du projet en 28 s au lieu de 12 min 33 s), mais le réglage de la racine est hérité
  par toutes les dépendances, dont les `.olean` ne sont alors plus matérialisés dans leurs
  `build/` : l'éditeur fonctionne (via `lake setup-file`), mais tout ce qui passe par `LEAN_PATH`
  casse — `lake env lean`, `lake exe checkdecls`, et vraisemblablement doc-gen4.
  `restoreAllArtifacts = true` ne corrige que le paquet racine, pas Mathlib/Batteries/Aesop. Ne pas
  l'activer.

## Carte du dépôt

| Fichier | Rôle | Analogue Mathlib |
|---|---|---|
| `TemporalGraph/Init.lean` | Rule-set aesop `TemporalGraph`, utilisé par la macro `aesop_temporal_graph` | `SimpleGraph/Init.lean` |
| `TemporalGraph/Basic.lean` | Type central `TemporalGraph V` (juste `Adj : V → V → ℕ → Prop`), classes `IsSymm`/`IsLoopless`, prédicats `IsSimple`/`IsClique`/`IsCliqueGraph`/`IsProper`/`IsHappy`, `EarliestEdge`/`LatestEdge`/`EarliestNeighbor`/`LatestNeighbor`, ordre `≤`/`⊥`, `footprint` (→ `Digraph`), `simpleFootprint` (→ `SimpleGraph`, via `SimpleGraph.fromRel`, sans hypothèse), `adjAt`, `symmetrize`, `fromEdgeSet`, `neighborSet`, `incidenceSet`, `arcSet`/`arcSize` (monde orienté), `edgeSet`/`size` (monde symétrique ; `mem_edgeSet` demande seulement `[IsSymm]`) ; `size`/`arcSize` sont des `def` calculables (pattern `SimpleGraph.degree` : `Fintype.card` sous une instance `[Fintype G.edgeSet]`/`[Fintype G.arcSet]`), avec la forme instance-free `Set.ncard` disponible via `size_eq_ncard`/`arcSize_eq_ncard` | `SimpleGraph`, mais sans `symm`/`loopless` bundlés |
| `TemporalGraph/NonemptyTemporalWalk.lean`, `TemporalGraph/TemporalWalk.lean` | Marches temporelles non strictes, à temps croissant ; prédicat `IsStrict` (temps strictement croissants, propagé de `NonemptyTemporalWalk` à `TemporalWalk`) et raccourcissement `NonemptyTemporalWalk.exists_isStrict` ; API `length`/`support`/`arcs`/`append`/`mapLe` (`length_append`, `arcs_append`, `*_mapLe`, `mapLe_append`, `mapLe_mapLe`, `start_mem_support`, `end_mem_support`, `adj_of_mem_arcs`) | `SimpleGraph.Walk` |
| `TemporalGraph/Subgraph.lean` | Sous-graphe temporel : `TemporalGraph.Subgraph` étend `TemporalGraph V`, ajoutant `verts`+preuves `adj_sub`/`edge_vert`/`edge_vert'` ; coercions (`coe`, `toTemporalGraph`), prédicats hérités `IsSymm`/`IsSimple`/`IsProper`/`IsHappy`, spécifiques au sous-graphe `IsCliqueSubgraph` ; `edgeSet`, `neighborSet`, `size`, `incidenceSet` sont hérités de `TemporalGraph` ; treillis borné et union `⊔` (`SemilatticeSup`), `induce`/`deleteVerts`/`addVerts`/`addArc`/`addEdge` ; monotonie `toTemporalGraph_le`/`toTemporalGraph_le_self` | `SimpleGraph.Subgraph` |
| `TemporalGraph/Bipartite.lean` | Bipartition temporelle `IsBipartiteWith`/`IsBipartite` (ensembles explicites, sans hypothèse de symétrie, non classe), pont `isBipartiteWith_iff_simpleFootprint` vers Mathlib, restriction `between` aux arcs entre deux ensembles, bi-cliques temporelles `IsBicliqueWith`/`IsBiclique` (SAND 2025 §1.1 ; prennent un ensemble de sommets), constructeur `completeBipartite` sur `α ⊕ β`, et au niveau `Subgraph` : `Subgraph.between` | `SimpleGraph/Bipartite.lean` |
| `TemporalGraph/Connectivity/Basic.lean`, `Connectivity/Subgraph.lean` | `Reachable` (avec monotonie `Reachable.mono`), `StrictReachable` et l'équivalence `reachable_iff_strictReachable` (graphe symétrique et propre ; `IsSymm` nécessaire), `TemporallyConnected` (prend un ensemble `S : Set V` ; shorthands `TemporallyConnectedGraph` pour `Set.univ` et `Subgraph.TemporallyConnectedSubgraph` pour `H.verts`) ; spanners au niveau sous-graphe sur `V` (`Subgraph.IsSpanner`, `Subgraph.IsSpannerOf`, `Subgraph.IsTCSpanner`) | `SimpleGraph.Connectivity` |
| `TemporalGraph/Dismountability/Basic.lean` | `Dismountable`, `TwoHopDismountable`, partition `vminus`/`vplus`/`vzero`, bijections earliest/latest-neighbor — correspond aux Lemmes 3.1, 3.2, 3.4 et au Corollaire 3.3 de SAND 2025 ; réciprocité `earliestEdge_reciprocity`/`latestEdge_reciprocity` (Lemme 3.5), `biclique_of_not_twoHopDismountable` (Corollaire 4.1), `between_TC_of_not_twoHopDismountable` (remarque après le Corollaire 4.1), `temporallyConnected_of_reachable_of_matchings` (§4.1) | — |
| `TemporalGraph/Dismountability/Operations.lean` | Opérations `dismount`/`mount`/`twoHopMount` et leurs théorèmes de correction (`dismountability`, `twoHopDismountability`), `mount_temporallyConnected`/`twoHopMount_temporallyConnected`, et `exists_isSpannerOf_of_twoHopDismountable` (SAND 2025, Théorème 2.1 et §2.1) | — |
| `TemporalGraph/Dismountability/OneSided.lean` | Dismountability *one-sided* (SAND 2025, §4.1) : spanner unilatéral `IsSpannerFromTo` (de `s` vers `t`), `OneSidedDismountable`, `oneSidedMount` (+ API, `oneSidedMount_size`), découpage `IsSpannerFromTo.sup` / `isSpannerFromTo_sup_of_induce`, étape `oneSidedDismountability`, pigeonnier `exists_oneSidedDismountable_of_ncard_lt`, assemblage `temporallyConnected_of_isSpannerFromTo` | — |
| `TemporalGraph/Dismountability/OneSidedBound.lean` | Borne `O(n log n)` (SAND 2025, §4.1) : récurrence `spannerBound` et `spannerBound_isBigO`, `IsOneSidedSpannerBound` / `exists_isBigO_isOneSidedSpannerBound` (bi-cliques), `exists_isSpannerFromTo_ncard_le` et `exists_isSpannerOf_of_not_twoHopDismountable`, puis `exists_isSpannerOf_ncard_le` (borne explicite `2n⌈log₂ n⌉ + 4n`) et `exists_isBigO_isSpannerOf` (cliques) | — |
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
  `bot`, `sup`, `symmetrize`, `between` (`TemporalGraph` et `Subgraph`), `completeBipartite`,
  `mount`, `twoHopMount`, `oneSidedMount`), si bien que la résolution les trouve en cascade — y compris à
  travers le terme à quatre couches que `twoHopMount` construit. Une instance unique de `loopless`
  en déduit la looplessness de tout sous-graphe.
- `TemporalGraph.Subgraph G` : s'étend maintenant de `TemporalGraph V`, héritant de son champ
  `Adj`. Huit définitions qui existaient identiquement aux deux niveaux (`IsSymm`, `IsSimple`,
  `IsProper`, `IsHappy`, `EarliestEdge`, `LatestEdge`, `EarliestNeighbor`, `LatestNeighbor`)
  sont donc supprimées de `Subgraph` ; elles sont maintenant héritées par
  la notation de champ généralisée via la projection `toTemporalGraph`. Restent définis en
  `Subgraph` les prédicats/définitions qui quantifient sur `H.verts` : `neighborSet`, `size`,
  `incidenceSet` (`edgeSet` n'est PAS redéfini : il est hérité de `TemporalGraph`, voir le
  commentaire de la `section edgeSet` de `Subgraph.lean`). Le champ de preuve `symm` a disparu : un sous-graphe
  peut donc être orienté. Comme `Adj.snd_mem` se déduisait de `symm`, la structure gagne en
  échange un champ de données `edge_vert' : Adj x y n → y ∈ verts` — l'invariant correct pour
  un objet orienté, et les six constructions le prouvent sans symétrie. Conséquence : `[Fact
  G.IsSymm]` disparaît entièrement du dépôt, `⊤ : Subgraph G` et `BoundedOrder` redeviennent
  inconditionnels.
- **Prédicats relatifs à un ensemble de sommets** : les prédicats qui quantifient sur les sommets
  prennent un `Set V` en argument, comme `SimpleGraph.IsClique` dans Mathlib (`G.IsClique S`,
  `G.IsBiclique S`). Leur version héritée est donc correcte sur un sous-graphe (`H.IsClique
  H.verts`) et aucun doublon `Subgraph` n'est nécessaire ; `Subgraph.IsClique` et
  `Subgraph.IsBiclique` ont été supprimés. Un prédicat « sur tout le type » redéfini dans
  `Subgraph` s'affiche sous le même nom que l'hérité (`H.IsClique`) et produit des erreurs
  incompréhensibles (« `H.IsClique` attendu, `H.IsClique` reçu »). `TemporallyConnected` suit
  maintenant cette convention : elle prend un ensemble `S : Set V`, avec shorthands `TemporallyConnectedGraph` (= `Set.univ`) et `Subgraph.TemporallyConnectedSubgraph` (= `H.verts`). Deux abréviations évitent de répéter l'ensemble : `G.IsCliqueGraph` (`G.IsClique Set.univ`) et `H.IsCliqueSubgraph` (`H.IsClique H.verts`). Elles portent des noms distincts exprès : un `Subgraph.IsClique` masquerait `TemporalGraph.IsClique`, et sur un sous-graphe `H.IsCliqueGraph` (hérité) signifie « clique sur tout `V` ».
- **Deux ensembles d'arêtes** : `arcSet : Set (V × V × ℕ)` et `arcSize` comptent les arcs
  (paires ordonnées) sans aucune hypothèse — c'est le monde orienté. `edgeSet : Set (Sym2 V × ℕ)`
  et `size` comptent les arêtes non orientées ; `mem_edgeSet` demande seulement `[G.IsSymm]`
  (pas `[G.IsLoopless]`) — c'est le monde symétrique.
- **Rien de central ne passe par le sous-type.** `Subgraph.Reachable`, `Subgraph.TemporallyConnected`,
  `Subgraph.size`, `Subgraph.neighborSet` et les relèvements de marches ont été supprimés : sur un
  sous-graphe, `H.Reachable x y` (sommets dans `V`), `H.size`, `H.neighborSet x` et
  `H.incidenceSet x` sont les notions héritées. Une notion qui porte sur des sommets donnés les
  prend dans `V` (avec des hypothèses d'appartenance) ; une notion qui quantifie sur les sommets
  prend un `Set V`. `H.coe : TemporalGraph H.verts` reste une petite API optionnelle (ponts
  `is*_iff_coe`, `coe_earliestEdge`…). Les bijections `earliestNeighborFn`/`latestNeighborFn`
  suivent aussi cette règle : ce sont des fonctions totales `V → V` (`earliestNeighborFn_bijOn`,
  `latestNeighborFn_bijOn` énoncent `Set.BijOn` entre `H.vplus` et `H.vminus`), sans passer par le
  sous-type.
- **Renommage ultérieur (commit `acb993a`)** : le constructeur à une seule orientation, sans
  aucune hypothèse de symétrie, s'appelle maintenant `addArc` (l'ancien `addEdge` générique), et
  le constructeur à deux orientations qui demande `[G.IsSymm]` s'appelle maintenant `addEdge`
  (l'ancien `addEdgeSymm`, corps de définition inchangé, argument de symétrie perdu au profit de
  l'instance) — et reste celui qu'utilisent `mount`/`twoHopMount`. Les lemmes ont suivi :
  `addEdge_edgeSet`, `addEdge_size`, `addEdge_size_le`
  (`Subgraph.lean`), `Reachable.addEdge` (`Connectivity/Subgraph.lean`) et l'instance
  `addEdge_isSymm` ; plus aucun nom ne porte le suffixe `addEdgeSymm`.
- `spanningCoe` a été supprimé, remplacé par la projection héritée `toTemporalGraph`. Les lemmes
  ont été renommés en conséquence : `top_spanningCoe` → `top_toTemporalGraph`,
  `size_of_spanningCoe` → `size_of_toTemporalGraph`. Les relèvements de marches
  (`lift_spanningCoe_walk` / `lift_toTemporalGraph_walk` / `lift_walk_toTemporalGraph` et variantes)
  ont été supprimés, remplacés par `Reachable.mono` : la réachabilité est monotone selon `≤`, et
  les nouvelles définitions walk-mapper `NonemptyTemporalWalk.mapLe` / `TemporalWalk.mapLe` produisent
  une marche plus lente. `spanningCoe_edgeSet_eq` a aussi été **supprimé**, `H.edgeSet`
  résolvant directement à travers la notation de champ généralisée (voir la `section edgeSet` de `Subgraph.lean`).

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
- **Champs sur `Std.Symm` / `Std.Irrefl`, comme `SimpleGraph`.** `IsSymm.symm : ∀ n, Std.Symm
  (G.adjAt n)` et `IsLoopless.loopless : ∀ n, Std.Irrefl (G.adjAt n)`, où
  `abbrev adjAt G n := fun x y => G.Adj x y n` est la tranche temporelle. Conventions :
  - **construire** un `IsSymm` avec `IsSymm.of_adj fun n x y h ↦ …` (ou `refine .of_adj ?_`), jamais
    avec des constructeurs anonymes imbriqués ;
  - **utiliser** `adj_symm`/`Adj.symm`/`adj_comm`, pas le champ ; le champ ne sert que si la
    symétrie est une hypothèse explicite : `(hs.symm n).symm _ _ h` ;
  - **API de Mathlib** : les instances `IsSymm.stdSymm`/`IsLoopless.stdIrrefl` exposent chaque
    tranche. Le temps étant le dernier argument, un lemme à relation implicite ne la trouve pas sur
    `G.Adj a b n` (l'unification d'ordre supérieur échoue) : nommer la relation
    (`comm_of (G.adjAt n)`, `Std.Symm.iff (r := G.adjAt n) a b`, `symm_of (G.adjAt n) h`,
    `irrefl_of (G.adjAt n) a`) ou énoncer le but avec `adjAt`.
- Les accesseurs gardent leur forme moins l'argument : `h.symm hs` → `h.symm`, `H.adj_symm hs h`
  → `H.adj_symm h`, `G.irrefl hl` → `G.irrefl`, `h.ne hl` → `h.ne`, `H.mem_edgeSet hsH hl` →
  `H.mem_edgeSet`.
- **Instances** : `addEdge` (l'ancien `addEdgeSymm`), `mount` et `twoHopMount` ont perdu leur
  argument de symétrie (`H.addEdgeSymm hs h h₁` autrefois, `H.addEdge h h₁` aujourd'hui). Chaque
  construction qui préserve
  la symétrie ou la looplessness déclare une instance correspondante ; la résolution la trouve en
  cascade.
- **Tactique `symm` : inutilisable sur `Adj`, et c'est voulu.** Aucun lemme n'est `@[symm]` et il
  n'y a pas de `macro_rules` (retirée : Mathlib n'étend pas `symm` ainsi, et ses lemmes `Std.Symm`
  ne sont pas `@[symm]` non plus). Sur un but `Adj`/`adjAt`, `symm` répond proprement « No
  applicable symmetry lemma » ; écrire le terme `h.symm` / `adj_symm h`. **Ne jamais mettre
  `@[symm]` sur un lemme qui prend une instance** (`[G.IsSymm]` ou `[Std.Symm (G.adjAt n)]`) : la
  tactique ne synthétise pas l'instance et le noyau rejette la preuve (`declaration has
  metavariables`, lean4#9997, PR de correction #13047 non fusionnée). `attribute [-symm]` est
  d'ailleurs refusé par Lean. Quand #13047 sera fusionnée, `@[symm]` sur `adj_symm` deviendra
  possible.
- **Règles aesop du rule-set `TemporalGraph` : `forward`, pas `apply`, pour tout lemme de la forme
  `H.Adj … → …`.** `adj_symm`, `Subgraph.Adj.adj_sub`, `Adj.fst_mem` et `Adj.snd_mem` sont des
  règles `safe forward` : à partir d'une hypothèse `h : H.Adj u v t`, aesop ajoute une fois
  `H.Adj v u t` (avec `[IsSymm]`), `G.Adj u v t`, `u ∈ H.verts` et `v ∈ H.verts`. En règles
  `apply`, elles cassaient aesop, vérifié en Lean : `adj_sub` (conclusion `G.Adj u v t`)
  s'unifiait avec n'importe quel but d'adjacence en inventant un sous-graphe `?H`, d'où une
  chaîne infinie et un timeout ; la symétrie en `apply` boucle ; et `fst_mem`, `safe` donc sans
  retour arrière, était choisi à tort sur un but `v ∈ H.verts`. `Subgraph.Adj.symm` n'a plus
  aucun attribut.

### Annotations `grind`

- Lemmes d'adjacence `H.Adj … → …` : `grind →` (miroir des règles aesop `safe forward`) ;
  `irrefl` : `grind .` ; `Adj.ne`/`Adj.ne'` (`TemporalGraph` et `Subgraph`) : `grind →` ; caractérisations `*_adj`/`*_verts` des constructions : `grind =` ;
  `grind ext` sur `TemporalGraph` seulement. **Jamais `grind ext` sur une structure qui porte des
  champs de preuve, comme `Subgraph`** (`adj_sub`, `edge_vert`, `edge_vert'`) : `grind` développe
  alors chaque terme `H : Subgraph G` en `⟨H.1, …⟩` (`propagateEtaStruct`), et les champs de preuve
  deviennent des lemmes locaux instanciés sur chaque `H.Adj …`. Les attributs `ext` survivent à
  `grind only` (`getOnlyExtensionState`, `Grind/Main.lean:39`). Mesuré (2026-10-02) : un
  `grind only` de `twoHopDismountability` passait de 0,27 s à 1,6 s (751 instances au lieu de 263).
  Au besoin, passer `Subgraph.ext` en paramètre local.
- Définitions de prédicats d'arêtes (`EarliestEdge`, `LatestEdge`, `*Neighbor`, `IsProper`,
  `IsSimple`) et équivalences d'ordre (`le_iff_adj`, `Subgraph.le_def`) : `grind =`. Jamais
  `grind unfold` (casse les appels `grind [Def]`), jamais `grind =` sur `adj_comm`. `vminus`/`vplus`
  ne sont volontairement pas annotées.
- Définitions récursives de marches (`length`, `support`, `arcs`, `append`, `mapLe`, …) : `grind =`,
  donc les lemmes d'API se prouvent par `induction p <;> grind`. Un lemme dont l'énoncé ne mentionne
  pas la marche (`nondecreasing_time`, `EarliestEdge.le_start`) ne peut pas être annoté : le passer en
  `have`. `grind` ne construit pas une marche (valeur dans `Type`) : les témoins de `Reachable`
  restent explicites.
- Preuves stables : `grind only […]` obtenu par `grind?` (retirer les ancres `#xxxx`).
  Toute preuve stable utilise `grind only […]`, liste coupée sur plusieurs lignes si besoin :
  jamais de repli sur `grind` nu pour une question de longueur. Exception : `induction p <;> grind`
  / `cases p <;> grind` pour des lemmes d'API purement calculatoires. Ne pas remplacer par `grind`
  une preuve courte qui porte l'argument du papier ; préférer un terme explicite quand il est aussi
  court ; commenter en une ligne l'étape mathématique quand `grind only` remplace un raisonnement ;
  pas de `simp` non restreint avant `grind`.

### Système de modules

- **Imports Mathlib précis, jamais `import Mathlib`** : `Basic` importe `Combinatorics.Digraph.Basic`,
  `Combinatorics.SimpleGraph.Basic` et `Data.Set.Card` ; chaque fichier ajoute ce qu'il utilise
  (`import` simple si seules les preuves en ont besoin). Le build est passé de 8977 à 2095 tâches.
- **Fichiers en modules** : tous sauf `Examples` et la racine `TemporalGraph.lean`, c'est-à-dire
  `Init`, `Basic`, `NonemptyTemporalWalk`, `TemporalWalk`, `Connectivity/*`, `Subgraph`,
  `Bipartite` et `Dismountability/*`. Un module n'importe que des
  modules, mais un non-module peut importer un module : on porte donc de bas en haut.
- **Motif (celui de Mathlib)** : copyright, `module`, imports en `public import` (en `import`
  simple s'ils ne servent qu'aux preuves), docstring de module, puis `@[expose] public section`
  sans `end`. Le `@[expose]` est indispensable : la bibliothèque déplie ses définitions d'un
  fichier à l'autre (`simp [def]`, `grind =`, `unfold`, égalités par définition), ce qu'un
  corps non exposé interdit. Tout nouveau fichier de la base suit ce motif.
- **Gain mesuré (2026-10-07)** : après une modification de preuve dans `Basic`, aucun des 6 modules
  en aval n'est recompilé ; seuls les non-modules le sont. `lake env lean` et `checkdecls` (les
  déclarations du blueprint) fonctionnent. doc-gen4 n'a pas encore été relancé sur les modules.
- Explications détaillées : note Obsidian `R&D/Annexes/systeme-de-modules-lean.md`.

### Autres conventions

- **Forme Mathlib** (2026-10-07) : `IsSimple`/`IsProper` sont curryfiés à binders stricts
  (`∀ ⦃x y n m⦄, G.Adj x y n → G.Adj x y m → n = m`) : s'appliquent en `h₀ h₁ h₂`. Constructeurs
  de marches en minuscules : `single`/`step` (`step` ajoute un arc à la fin) et `nil`/`ofNonempty`.
  Lemmes de construction (`addEdge_le`, `deleteVerts_le`, …) à arguments implicites, comme dans
  Mathlib, sans doublon primé : passer les arguments par nom (`addEdge_le (h := h₀) (h₁ := …)`).
  L'ordre strict de `Subgraph` est celui par défaut ; sa forme explicite est le lemme `lt_iff`.

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
numérotation de **SAND 2025** (Carnevale–Casteigts–Corsini) dans sa **version publiée LIPIcs**
(https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.SAND.2025.6), numérotée par section
(`Lemma 3.4`, `Corollary 4.1`, …). **Ne pas prendre les numéros de la version arXiv**
(2502.01321) : elle utilise un compteur unique (`Lemma 5`, `Corollary 12`, …), et un premier
alignement fait sur l'arXiv était faux pour cette raison. La définition de la dismountability et
de la partition `V⁻`/`V⁺`/`V⁰` sont en prose, non numérotées ; la connexité temporelle de la
bi-clique entre `V⁻` et `V⁺` est une remarque en prose juste après le Corollaire 4.1.

| Code (`Dismountability/Basic.lean` sauf mention contraire) | SAND 2025 |
|---|---|
| `Dismountable` | §2, 1-hop dismountability (hypothèse du Théorème 2.1) |
| `TwoHopDismountable` | §2.1, {1,2}-hop dismountability (cas `k ≤ 2` de la k-hop dismountability) |
| `vminus`, `vplus`, `vzero` | §3.1, définis juste avant le Lemme 3.1 (`V⁻ = {n⁻(v)}`, `V⁺ = {n⁺(v)}`, `V⁰` le reste) |
| `partition_of_not_dismountable` | Lemme 3.1 |
| `vplus_ne_neighbor_of_not_twoHopDismountable`, `vminus_ne_neighbor_of_not_twoHopDismountable` | Lemme 3.2 |
| `existsUnique_vplus_earliestEdge`, `existsUnique_vminus_latestEdge` | Corollaire 3.3 (1) et (2) : couplages parfaits entre `V⁻` et `V⁺` |
| `earliestNeighborFn_bijOn`, `latestNeighborFn_bijOn` | Corollaire 3.3 (`Set.BijOn` bijections entre les ensembles `V⁺` et `V⁻`, via Lemme 3.2) |
| `vminus_card_eq_vplus_card` | Corollaire 3.3 (3) : `|V⁻| = |V⁺|` |
| `vzero_empty_of_not_twoHopDismountable` | Lemme 3.4 |
| `dismountability` (`Dismountability/Operations.lean`) | Théorème 2.1 |
| `twoHopDismountability` (`Dismountability/Operations.lean`) | §2.1, cas 2-hop (non numéroté) |
| `exists_isSpannerOf_of_twoHopDismountable` (`Dismountability/Operations.lean`) | Théorème 2.1 et §2.1 (cas mixte : tout spanner de `H.dismount x` s'étend en un spanner de `H` avec au plus 4 arêtes de plus) |
| `temporallyConnected_of_reachable_of_matchings` | §4.1, après le Corollaire 4.1 (connexité temporelle de `s ∪ t` à partir des couplages `M⁻`/`M⁺` et de `s` atteignant `t`) |
| `exists_isSpannerOf_of_not_twoHopDismountable` (`Dismountability/OneSidedBound.lean`) | §4.1 (clique non {1,2}-hop dismountable : spanner one-sided de la bi-clique plus les couplages) |
| `exists_isSpannerOf_ncard_le` (`Dismountability/OneSidedBound.lean`) | §4.1, borne explicite `2n⌈log₂ n⌉ + 4n` |
| `earliestEdge_reciprocity`, `latestEdge_reciprocity` | Lemme 3.5 (Reciprocity), énoncés (1) et (2) |
| `biclique_of_not_twoHopDismountable` | Corollaire 4.1 (bi-clique entre `V⁻` et `V⁺`) |
| `between_TC_of_not_twoHopDismountable` | remarque en prose après le Corollaire 4.1 |
| `oneSidedDismountability`, `exists_oneSidedDismountable_of_ncard_lt` (`Dismountability/OneSided.lean`) | §4.1, dismountability *one-sided* d'Angrick et al. (non numéroté) |
| `exists_isBigO_isOneSidedSpannerBound`, `exists_isBigO_isSpannerOf` (`Dismountability/OneSidedBound.lean`) | §4.1, spanners `O(n log n)` des bi-cliques puis des cliques (non numéroté) |

Toute nouvelle preuve visant un résultat du papier (ou d'un résultat récent connexe) cite le
numéro exact dans une **docstring Mathlib** qui commence par la référence complète, puis énonce le
résultat en une phrase : `/-- SAND 2025, Lemma 3.4: in a clique that is not {1,2}-hop
dismountable, V⁰ = ∅. -/`. Toujours écrire la forme complète `SAND 2025, Lemma 3.4` (et non
`lemma 3.4` seul), pour qu'on ne confonde pas avec la numérotation de l'article CPS.

**Forme des énoncés** (appliquée à `Dismountability/Basic.lean`, à suivre partout) :
- ordre des binders : `{H : Subgraph G}` d'abord (les classes en dépendent), puis les classes
  (`[Finite H.verts] [Nontrivial H.verts] [H.IsSymm]`), puis les autres implicites
  (`{u v : V} {n : ℕ}`), puis les hypothèses explicites ;
- hypothèses nommées numérotées `h₀, h₁, h₂, …` sans trou ; si l'on en retire une, renuméroter ;
- binders courts regroupés sur une ligne (dans la limite de 100 caractères), binder long seul sur
  sa ligne.

## Commandes utiles

- Le toolchain Lean (`lean`, `lake`, `elan`) est dans `~/.elan/bin`, pas forcément sur le `PATH`
  d'un sous-shell : utiliser `~/.elan/bin/lake ...` au besoin.
- `lake build` : build complet, vert, et il couvre bien tous les modules depuis l'ajout des
  `globs` au `lakefile.toml`.
- `lake build TemporalGraph.Dismountability.Operations` : un module précis, avec ses dépendances.
- `lake env lean TemporalGraph/<Fichier>.lean` : typechecker un fichier isolé (demande que les
  `.olean` de ses dépendances existent déjà).
- Blueprint : projet uv dans `blueprint/` (`pyproject.toml` + `uv.lock`, pas de
  `requirements.txt`). Depuis la racine : `uv run --project blueprint leanblueprint web`, puis
  `lake env lean --run scripts/CheckDecls.lean blueprint/lean_decls` pour vérifier que les
  déclarations citées existent. **Ne plus utiliser `leanblueprint checkdecls`** : `lake exe
  checkdecls` importe toutes les bibliothèques du paquet, dont `Challenge` et `Solution`, qui
  définissent les mêmes noms (exigence de Comparator) ; l'import commun échoue sur ces doublons.
  Le script n'importe que `TemporalGraph`.
- Soumission Palomar (dépôt unique) : `Challenge.lean` (énoncé, imports Mathlib seuls, `sorry`
  volontaires), `Solution.lean` (mêmes énoncés, prouvés), `comparator.json`, `formalization.yaml`
  (brouillon : champs `TODO(archimage)` à compléter). `Solution.lean` recopie à l'identique les
  définitions de `Challenge.lean` et contient tout le pont avec la bibliothèque (aucun fichier
  propre à la soumission dans `TemporalGraph/`) ; toute modification d'une définition doit être
  reportée dans les deux fichiers. Tout fichier `.lean` du dépôt doit rester un module
  (`Examples` et la racine compris).
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
- `lake build` n'accepte pas `-j` (vérifié en `v4.29.0-rc6`).
- **Comptage d'arêtes : pattern `SimpleGraph.degree`, pas de `noncomputable` exposé.** `size`/
  `arcSize` sont des `def` calculables, `Fintype.card G.edgeSet`/`G.arcSet` sous une instance
  `[Fintype …]` (Mathlib, `Finite.lean:242` : `degree`/`card_neighborSet_eq_degree`/
  `ncard_neighborSet`) ; le pont instance-free est `size_eq_ncard`/`arcSize_eq_ncard`
  (`G.size = G.edgeSet.ncard`). Les lemmes de comptage de la bibliothèque (`addEdge_size`,
  `mount_size`, `twoHopMount_size`, `oneSidedMount_size`, …) sont désormais chacun doublés d'une
  version instance-free sur `edgeSet.ncard` (`ncard_edgeSet_addEdge`, `ncard_edgeSet_mount_le`,
  `ncard_edgeSet_twoHopMount_le`, `ncard_edgeSet_oneSidedMount_le`, …), dans laquelle `rw`/`simp`
  avec une égalité d'ensembles (par exemple `addEdge_edgeSet`, `mount_edgeSet`) passe directement
  sous `.ncard` sans détour par `Nat.card` ; la version `size` en est un corollaire sous
  `[Fintype …]`, via `size_eq_ncard`.
- CI GitHub Actions existante (ne pas modifier sans raison) : `lean_action_ci.yml` (build +
  docgen), `create-release.yml` (tag de release sur changement de `lean-toolchain`),
  `update.yml` (PR/issue automatique sur mise à jour Mathlib).
