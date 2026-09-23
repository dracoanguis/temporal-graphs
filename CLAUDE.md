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

## Carte du dépôt

| Fichier | Rôle | Analogue Mathlib |
|---|---|---|
| `TemporalGraph/Init.lean` | Rule-set aesop `LooplessTemporalGraph` (nom hérité, voir Conventions) | `SimpleGraph/Init.lean` |
| `TemporalGraph/Basic.lean` | Type central `TemporalGraph V` (juste `Adj : V → V → ℕ → Prop`), prédicats `IsSymm`/`IsLoopless`/`IsSimple`/`IsClique`/`IsProper`/`IsHappy`, `EarliestEdge`/`LatestEdge`/`EarliestNeighbor`/`LatestNeighbor`, ordre `≤`/`⊥`, `Footprint` (→ `Digraph`), `NeighborhoodSet`, `EdgeSet`, `size` | `SimpleGraph`, mais sans `symm`/`loopless` bundlés |
| `TemporalGraph/NonemptyTemporalWalk.lean`, `TemporalGraph/TemporalWalk.lean` | Marches temporelles non strictes, à temps croissant | `SimpleGraph.Walk` |
| `TemporalGraph/SubTemporalGraph.lean` | Sous-graphe temporel : `SubTemporalGraph` étend `TemporalGraph V`, ajoutant `Verts`+preuves `adj_sub`/`edge_vert`/`edge_vert'` ; coercions (`coe`, `toTemporalGraph`), prédicats hérités `IsSymm`/`IsSimple`/`IsProper`/`IsHappy`, spécifiques au sous-graphe `IsClique`/`NeighborhoodSet`/`EdgeSet`/`size`/`IncidenceSet` ; treillis borné, `induce`/`deleteVerts`/`addVerts`/`addEdge`/`addEdgeSymm` | `SimpleGraph.Subgraph` |
| `TemporalGraph/Connectivity/Basic.lean`, `Connectivity/SubTemporalGraph.lean` | `Reachable`, `TemporallyConnected`, spanners (`IsSpanner`, `IsTCSpanner`) | `SimpleGraph.Connectivity` |
| `TemporalGraph/Dismountability/Basic.lean` | `Dismountable`, `TwoHopDismountable`, partition `Vminus`/`Vplus`/`Vzero`, bijections earliest/latest-neighbor — correspond au Théorème 2.1 et aux Lemmes 3.1–3.4 du papier | — |
| `TemporalGraph/Dismountability/Operations.lean` | Opérations `dismount`/`mount`/`twoHopMount` et leurs théorèmes de correction (`dismountability`, `twoHopDismountability`) | — |
| `TemporalGraph.lean` (racine) | Fichier de démo/scratch, largement commenté ; seul module atteint par `lake build` (voir ci-dessous) | — |

## État actuel : refactor terminé

La bibliothèque a été entièrement refondue selon le pattern **unbundled** : aucune structure ne
porte de champs pour les propriétés algébriques (symétrie, looplessness), ceux-ci sont toujours
des prédicats externes passés explicitement en hypothèse.

- `TemporalGraph V` : type nu (`Adj : V → V → ℕ → Prop` seul) + prédicats externes `IsSymm` /
  `IsLoopless` / `IsSimple` / etc. (voir `Basic.lean`)
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
- `addEdge` a été généralisé pour ajouter une SEULE orientation, sans aucune hypothèse de
  symétrie ; `addEdgeSymm` (l'ancien `addEdge`, corps de définition inchangé) ajoute les deux
  orientations, requiert `G.IsSymm`, et reste celui qu'utilisent `mount`/`twoHopMount`.
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

- Dot-notation façon Mathlib : `protected theorem Adj.ne`, `Adj.symm`, etc. Les hypothèses de
  propriété se placent avant l'argument principal, pour que `h.symm hs` fonctionne.
- Attributs `@[ext]`, `@[simp]` posés comme dans les fichiers `SimpleGraph`. En revanche **ne pas
  poser `@[symm]` sur un lemme portant une hypothèse latérale** (comme `adj_symm (hs : …)`) :
  vérifié expérimentalement, la tactique `symm` ne sait pas décharger cette hypothèse — même
  présente dans le contexte local — elle la laisse en métavariable non assignée et la déclaration
  échoue plus tard au noyau (`(kernel) declaration has metavariables`). Utiliser la forme
  explicite `h.symm hs`. Le `@[symm]` restant sur `TemporalGraph.adj_symm` (`Basic.lean`) est un
  piège latent de même nature.
- Arêtes non orientées représentées par `Sym2 V` ; `EdgeSet : Set (Sym2 V × ℕ)`.
- **Conséquence de l'héritage dans `SubTemporalGraph`** : depuis que `H.Adj x y n` est le
  `Adj` du parent `TemporalGraph`, les lemmes du namespace `SubTemporalGraph.Adj.*` ne sont
  PLUS accessibles via notation pointée sur une preuve `h : H.Adj x y n`. Il faut écrire
  explicitement `H.adj_sub h`, `H.edge_vert h`, `H.edge_vert' h`, `H.adj_symm hs h` (et non
  `h.adj_sub`, `h.fst_mem`, `h.snd_mem`, `h.symm hs`). Les formes qualifiées complètes
  (`SubTemporalGraph.Adj.snd_mem h`) continuent de fonctionner. C'est le revers de la médaille :
  le lemme corpus du parent s'applique à `H.Adj` gratuitement précisément parce que le type n'en
  distingue plus l'adjacence du sous-graphe de celle d'un graphe.
- Automatisation via la macro `aesop_temporal_graph`, qui utilise le rule-set aesop
  `LooplessTemporalGraph` déclaré dans `Init.lean` — ce nom de rule-set est resté sur l'ancien
  nom du type ; à renommer plus tard si on veut de la cohérence stricte, mais ce n'est pas
  bloquant (c'est juste une étiquette de rule-set, pas une référence de type).

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
- `lake build` : build complet (échoue actuellement à cause de `TemporalGraph.lean`, voir
  ci-dessus).
- `lake env lean TemporalGraph/<Fichier>.lean` : typechecker un fichier isolé sans dépendre du
  reste — utile tant que le refactor n'est pas terminé.
- CI GitHub Actions existante (ne pas modifier sans raison) : `lean_action_ci.yml` (build +
  docgen), `create-release.yml` (tag de release sur changement de `lean-toolchain`),
  `update.yml` (PR/issue automatique sur mise à jour Mathlib).
