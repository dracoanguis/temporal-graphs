import TemporalGraph.Basic


namespace SimpleTemporalGraph


variable {V W X : Type*} (G : SimpleTemporalGraph V) (G' : SimpleTemporalGraph W) {u v : V}

protected def comap (f : V → W) (G : SimpleTemporalGraph W) : SimpleTemporalGraph V where
  Adj u v t := G.Adj (f u) (f v) t
  symm t _ _ h := G.symm t h
  loopless _ _ := G.loopless _ _

abbrev induce (s : Set V) (G : SimpleTemporalGraph V) : SimpleTemporalGraph s :=
  G.comap (Function.Embedding.subtype _)

end SimpleTemporalGraph
