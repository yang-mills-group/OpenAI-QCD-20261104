import YM.Pods.Coins
/-! # Two chess-board applications: bare fine theory and margin-bearing normalized coherent histories. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Romance
open QCD QCD.Lat QCD.RP QCD.Grass Lattice Wilson MeasureTheory Function Filter Finset NormedSpace
open Chess Cells Tiling Chess.Fortuna
open scoped BigOperators Topology Matrix.Norms.L2Operator ComplexOrder Classical
variable {A : Type*} {n : Side} {F : ℕ} {x y : Insertion n F}
variable {p k r:ℕ} (T : Tiling n) (V : Insertion n F→ₗ[ℂ]ℂ)(R: Regulator n F)
lemma reachSmall (p:T.Cell)(a:Axis)(r:ℕ) : (⋃ v∈T.plusCells p a,T.margin v r) ⊆ (T.bandCut p a).sector:=by
   intro x hx; obtain ⟨v,hv⟩:= Set.mem_iUnion.1 hx; obtain ⟨hr,hx⟩:= Set.mem_iUnion.1 hv; exact T.within p a v ((T.positive_side ..).1 hr) hx.1

lemma zero_margin (x:T.Cell)(h:T.kind=.link): T.margin x 0 =T.chamber x:=by
   refine Set.Subset.antisymm (fun v h=>h.1) (fun v h' =>?_) -- v implicit
   refine ⟨h',fun i=> ⟨by omega,?_⟩⟩; have he:= T.small h' i; rw [h,Nat.add_zero]; exact he

lemma bareSeal (h : T.kind=.link)(hb:0≤R.β)(hl:4≤n.val)(k:ℕ): Chess.Fortuna.Seal R.raw R T k := ⟨fun p a f g hf hq hv ht=> Regulator.schwarz h hb (by have h:=(T.bandCut p a).even; omega : 2 ≤ (T.bandCut p a).half.val) _ _ (lower_maps hf (reachSmall T ..)) (lower_maps hv (reachSmall T ..)) hq ht⟩
lemma averageSeal (h : T.kind=.link)(hb:0≤R.β)(hl:4≤n.val)(k:ℕ): Chess.Fortuna.Seal R.average R T k := by
    refine ⟨fun p a f g h1 h2 h3 h4=>?_⟩
    intro w; let P:=fun x y:Insertion n F=> R.raw (picture (T.bandCut p a) R.zeroCut x*y); have H(x y:Insertion n F): ‖w x y‖= ‖R.Z⁻¹‖*‖P x y‖:= norm_smul R.Z⁻¹ (P x y); simp_rw [H]
    have he:‖P f g‖^2 ≤ ‖P f f‖*‖P g g‖:= (bareSeal T R h hb hl k).sewn p a f g h1 h2 h3 h4; nlinarith only [mul_le_mul_of_nonneg_left he (sq_nonneg ‖R.Z⁻¹‖)]

structure Base (x:T.Cell)(v:ℕ) (A:Insertion n F) :Prop where
    floors : Floors (T.margin x v) A
    invariant: Lat.Invariant A
    parity : Chess.Parity A

lemma figure (h:T.kind=.link)(P:A→T.Cell)(f:A→Insertion n F)(he:∀ i,Base T (P i) k (f i))(hR:R.t=0): Figure R T k (fun i=> moved T R.zeroCut (f i) (P i)):=by
   refine ⟨stabilizes T h R hR P f (fun i=>⟨lower_maps (he i).floors (fun _ hx=> hx.1),(he i).invariant,(he i).parity⟩),?_⟩
   intro i p; have hc:= reach_in R.zeroCut (f i) (Romance.tag T (P i) p) (P i) (margins T k) (he i).floors; rw [tag_spec] at hc; exact hc

abbrev replicateR (A:Insertion n F)(p:T.Cell)(v:T.Cell):= moved T R.zeroCut A p v
abbrev floorL (x:Insertion n F)(p:T.Cell):ℝ:= Chess.Fortuna.Array.rootL (T:=T) V (fun (_ : Unit)=> replicateR T R x p) ⟨⟩
lemma floor_nn (x:Insertion n F)(p:T.Cell): 0≤ floorL T V R x p:= Real.rpow_nonneg (norm_nonneg _) _
lemma many (h:T.kind=.link)(f:T.Cell→Insertion n F)(he:∀ i,Base T i k (f i))(hR:R.t=0)(hv:Chess.Fortuna.Seal V R T k):
    ‖V ((Finset.univ.toList.map f).prod)‖ ≤ ∏ i:T.Cell,floorL T V R (f i) i:=by
    let X:= fun i=> replicateR T R (f i) i; have hz:=(Chess.Fortuna.Array.operation id (K:=X) (figure T R h id f he hR) V hv)
    have hh: (fun i=> X (id i) i)=f:=funext fun i=>moved_at ..
    rw [Chess.Fortuna.Array.costL, Chess.Array.use,hh] at hz; exact hz

theorem raw_mesh (h:T.kind=.link)(f:T.Cell→Insertion n F)(he:∀ i,SameTile T i (f i))(hR:R.t=0)(hb:0≤R.β)(hl:4≤n.val) : ‖R.average ((Finset.univ.toList.map f).prod)‖ ≤ ∏ i:T.Cell,floorL T R.average R (f i) i:= many T R.average R h f (fun i=> ⟨by rw [zero_margin T i h]; exact (he i).floors,(he i).inv,(he i).parity⟩) hR (averageSeal T R h hb hl 0)
abbrev tally (f:T.Cell→Insertion n F):= (Finset.univ.toList.map f).prod
lemma always_one (x y:T.Cell): replicateR T R (1:Insertion n F) x y=1:=by
   suffices h:∀ l:List (Band n),reels R.zeroCut l 1=(1:Insertion n F) by exact h _
   intro l; induction l with | nil=> rfl | cons a l ih=> simp [reels,ih,pic_one]
lemma roof_power (p:T.Cell)(x:Insertion n F): floorL T V R x p^ Fintype.card T.Cell=‖V (tally T (replicateR T R x p))‖:= Chess.Fortuna.Array.poweringL V (T:=T) (K:=fun _ : Unit=> replicateR T R x p) ⟨⟩ -- may elaborate wrong
lemma roof_blank (p:T.Cell)(h:V 1=1): floorL T V R 1 p=1:=by unfold floorL Chess.Fortuna.Array.rootL Chess.Fortuna.Array.costL Chess.Array.use; simp_rw [always_one]; simp [h]

end YM.Massive.Romance
#print axioms YM.Massive.Romance.raw_mesh
#print axioms YM.Massive.Romance.roof_power
#print axioms YM.Massive.Romance.roof_blank
