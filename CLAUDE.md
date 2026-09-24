# temporal-graphs

Bibliothèque Lean 4 + Mathlib sur les **graphes temporels** (arêtes étiquetées par un temps
`ℕ`). C'est un *rework* d'une bibliothèque précédente de l'auteur. L'objectif final n'est pas
figé au-delà de : prouver des résultats récents sur les graphes temporels — en particulier une
borne de spanner `O(n log n)` pour les cliques temporelles, via la technique de
*« dismountability »* de **Casteigts, Peters & Schoeters, *Temporal Cliques Admit Sparse
Spanners*, ICALP 2019 / JCSS**. Le scope peut s'élargir à d'autres résultats récents au fil du
travail.

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
| `TemporalGraph/Basic.lean` | Type central `TemporalGraph V` (juste `Adj : V → V → ℕ → Prop`), classes `IsSymm`/`IsLoopless`, prédicats `IsSimple`/`IsClique`/`IsProper`/`IsHappy`, `EarliestEdge`/`LatestEdge`/`EarliestNeighbor`/`LatestNeighbor`, ordre `≤`/`⊥`, `Footprint` (→ `Digraph`), `NeighborhoodSet`, `ArcSet`/`arcSize` (monde orienté), `EdgeSet`/`size` (monde symétrique, demande `[IsSymm]` et `[IsLoopless]`) | `SimpleGraph`, mais sans `symm`/`loopless` bundlés |
| `TemporalGraph/NonemptyTemporalWalk.lean`, `TemporalGraph/TemporalWalk.lean` | Marches temporelles non strictes, à temps croissant | `SimpleGraph.Walk` |
| `TemporalGraph/SubTemporalGraph.lean` | Sous-graphe temporel : `SubTemporalGraph` étend `TemporalGraph V`, ajoutant `Verts`+preuves `adj_sub`/`edge_vert`/`edge_vert'` ; coercions (`coe`, `toTemporalGraph`), prédicats hérités `IsSymm`/`IsSimple`/`IsProper`/`IsHappy`, spécifiques au sous-graphe `IsClique`/`NeighborhoodSet`/`EdgeSet`/`size`/`IncidenceSet` ; treillis borné, `induce`/`deleteVerts`/`addVerts`/`addEdge`/`addEdgeSymm` | `SimpleGraph.Subgraph` |
| `TemporalGraph/Connectivity/Basic.lean`, `Connectivity/SubTemporalGraph.lean` | `Reachable`, `TemporallyConnected`, spanners (`IsSpanner`, `IsTCSpanner`) | `SimpleGraph.Connectivity` |
| `TemporalGraph/Dismountability/Basic.lean` | `Dismountable`, `TwoHopDismountable`, partition `Vminus`/`Vplus`/`Vzero`, bijections earliest/latest-neighbor — correspond au Théorème 2.1 et aux Lemmes 3.1–3.4 du papier | — |
| `TemporalGraph/Dismountability/Operations.lean` | Opérations `dismount`/`mount`/`twoHopMount` et leurs théorèmes de correction (`dismountability`, `twoHopDismountability`) | — |
| `TemporalGraph.lean` (racine) | Fichier de démo/scratch, largement commenté ; le graphe `Square` y porte ses propriétés comme instances | — |

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
  `addVerts`, `deleteVerts`, `addEdgeSymm`, `fromEdgeSet`, `toSubTemporalGraph`, `coe`, `top`,
  `bot`, `mount`, `twoHopMount`), si bien que la résolution les trouve en cascade — y compris à
  travers le terme à quatre couches que `twoHopMount` construit. Une instance unique de `loopless`
  en déduit la looplessness de tout sous-graphe.
- `SubTemporalGraph G` : s'étend maintenant de `TemporalGraph V`, héritant de son champ `Adj`.
  Huit définitions qui existaient identiquement aux deux niveaux (`IsSymm`, `IsSimple`,
  `IsProper`, `IsHappy`, `EarliestEdge`, `LatestEdge`, `EarliestNeighbor`, `LatestNeighbor`)
  sont donc supprimées de `SubTemporalGraph` ; elles sont maintenant héritées par
  la notation de champ généralisée via la projection `toTemporalGraph`. Restent définis en
  `SubTemporalGraph` les prédicats/définitions qui quantifient sur `H.Verts` : `IsClique`,
  `NeighborhoodSet`, `EdgeSet`, `size`, `IncidenceSet`. Le champ de preuve `symm` a disparu : un
  sous-graphe peut donc être orienté. Comme `Adj.snd_mem` se déduisait de `symm`, la structure
  gagne en échange un champ de données `edge_vert' : Adj x y n → y ∈ Verts` — l'invariant correct
  pour un objet orienté, et les six constructions le prouvent sans symétrie. Conséquence :
  `[Fact G.IsSymm]` disparaît entièrement du dépôt, `⊤ : SubTemporalGraph G` et `BoundedOrder`
  redeviennent inconditionnels.
- **Deux ensembles d'arêtes** : `ArcSet : Set (V × V × ℕ)` et `arcSize` comptent les arcs
  (paires ordonnées) sans aucune hypothèse — c'est le monde orienté. `EdgeSet : Set (Sym2 V × ℕ)`
  et `size` comptent les arêtes non orientées ; `mem_edgeSet` demande `[G.IsSymm]` et
  `[G.IsLoopless]` — c'est le monde symétrique.
- `addEdge` a été généralisé pour ajouter une SEULE orientation, sans aucune hypothèse de
  symétrie ; `addEdgeSymm` (l'ancien `addEdge`, corps de définition inchangé) ajoute les deux
  orientations, perd son argument de symétrie (résolu maintenant en instance), et reste celui
  qu'utilisent `mount`/`twoHopMount`.
- `spanningCoe` a été supprimé, remplacé par la projection héritée `toTemporalGraph`. Les lemmes
  ont été renommés en conséquence : `top_spanningCoe` → `top_toTemporalGraph`,
  `spanningCoe_edgeSet_eq` → `edgeSet_toTemporalGraph`, `size_of_spanningCoe` →
  `size_of_toTemporalGraph`, `lift_spanningCoe_walk` → `lift_toTemporalGraph_walk`,
  `lift_walk_spanningCoe` → `lift_walk_toTemporalGraph`.

Chaque module typecheck et il n'existe aucun `sorry`. **Piège de vérification corrigé au passage** :
le `lean_lib` n'avait pas de `globs`, si bien que `lake build` ne compilait que le module racine et
ses imports — ce qui s'arrête à `SubTemporalGraph`. `Connectivity/*` et `Dismountability/*`
n'étaient donc jamais construits, ni en local ni en CI. Le `lakefile.toml` déclare désormais
`globs = ["TemporalGraph.+"]` : un `lake build` nu couvre tout. Si un doute subsiste sur un module
précis, le nommer explicitement (`lake build TemporalGraph.Dismountability.Operations`).

## Conventions de nommage/style observées

### Propriétés comme classes

- `IsSymm` et `IsLoopless` sont des **classes de type**, résolues en instances plutôt que filetées
  en hypothèses nommées. Les résultats qui en ont besoin prennent `[G.IsSymm]` / `[G.IsLoopless]`
  au lieu d'une hypothèse `(hs : G.IsSymm)`.
- Les accesseurs gardent leur forme moins l'argument : `h.symm hs` → `h.symm`, `H.adj_symm hs h`
  → `H.adj_symm h`, `G.irrefl hl` → `G.irrefl`, `h.ne hl` → `h.ne`, `H.mem_edgeSet hsH hl` →
  `H.mem_edgeSet`.
- **Instances** : `addEdgeSymm`, `mount` et `twoHopMount` ont perdu leur argument de symétrie
  (`H.addEdgeSymm hs h h₁` → `H.addEdgeSymm h h₁`). Chaque construction qui préserve la symétrie
  ou la looplessness déclare une instance correspondante ; la résolution la trouve en cascade.
- `@[symm]` s'applique à nouveau à `adj_symm` : l'argument est une instance (résolue), pas une
  hypothèse latérale (métavariable non assignée). Le piège historique — **ne pas mettre `@[symm]`
  sur un lemme avec une hypothèse latérale** — ne s'applique plus à celui-ci, mais reste vrai pour
  tout lemme avec un argument non-instance nécessaire pour fermer la preuve.

### Autres conventions

- Dot-notation façon Mathlib : `protected theorem Adj.ne`, etc. (pour les lemmes récursif sur
  l'adjacence).
- Attributs `@[ext]`, `@[simp]` posés comme dans les fichiers `SimpleGraph`.
- Arêtes non orientées représentées par `Sym2 V` ; `EdgeSet : Set (Sym2 V × ℕ)` (monde symétrique) ;
  `ArcSet : Set (V × V × ℕ)` (monde orienté).
- **Conséquence de l'héritage dans `SubTemporalGraph`** : depuis que `H.Adj x y n` est le
  `Adj` du parent `TemporalGraph`, les lemmes du namespace `SubTemporalGraph.Adj.*` ne sont
  PLUS accessibles via notation pointée sur une preuve `h : H.Adj x y n`. Il faut écrire
  explicitement `H.adj_sub h`, `H.edge_vert h`, `H.edge_vert' h`, `H.adj_symm h` (et non
  `h.adj_sub`, `h.fst_mem`, `h.snd_mem`, `h.symm`). Les formes qualifiées complètes
  (`SubTemporalGraph.Adj.snd_mem h`) continuent de fonctionner. C'est le revers de la médaille :
  le lemme corpus du parent s'applique à `H.Adj` gratuitement précisément parce que le type n'en
  distingue plus l'adjacence du sous-graphe de celle d'un graphe.
- Automatisation via la macro `aesop_temporal_graph`, qui utilise le rule-set aesop
  `TemporalGraph` déclaré dans `Init.lean`.

## Repères papier ↔ code

Les commentaires numérotés dans `Dismountability/Basic.lean` renvoient à
Casteigts–Peters–Schoeters :

| Commentaire dans le code | Contenu |
|---|---|
| `-- Theorem 2.1` | `Dismountable` |
| `-- def 3.1` | `Vminus`, `Vplus`, `Vzero` |
| `-- lemma 3.1` | `partition_of_not_dismountable` |
| `-- lemma 3.2` | `vplus_ne_neighbor_of_not_twoHopHismountable`, `vminus_ne_neighbor_of_not_twoHopDismountable` |
| `-- lemma 3.4` | `vzero_empty_of_not_twoHopDismountable` |

Toute nouvelle preuve visant un résultat du papier (ou d'un résultat récent connexe) devrait
garder cette convention : un commentaire citant le numéro exact du théorème/lemme visé.

## Commandes utiles

- Le toolchain Lean (`lean`, `lake`, `elan`) est dans `~/.elan/bin`, pas forcément sur le `PATH`
  d'un sous-shell : utiliser `~/.elan/bin/lake ...` au besoin.
- `lake build` : build complet, vert, et il couvre bien tous les modules depuis l'ajout des
  `globs` au `lakefile.toml`.
- `lake build TemporalGraph.Dismountability.Operations` : un module précis, avec ses dépendances.
- `lake env lean TemporalGraph/<Fichier>.lean` : typechecker un fichier isolé (demande que les
  `.olean` de ses dépendances existent déjà).
- CI GitHub Actions existante (ne pas modifier sans raison) : `lean_action_ci.yml` (build +
  docgen), `create-release.yml` (tag de release sur changement de `lean-toolchain`),
  `update.yml` (PR/issue automatique sur mise à jour Mathlib).
