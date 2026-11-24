import YM.QCD.Grove.Dust
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Grove
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun Kites
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {I J V:Type}{c f:Side}{N n:ℕ}
open Animals
open Flume Orbit Quarry Folding Further.PhysicalPeriodLimitF933 Macrame PhysicalNext.Repeat Deck Meadow
open Pressure ConnectedActivityE6 Blaze King Push.Uniform
open Brick Dust Slide Trio.Sharp
-- layout
variable {C:Side}{D D' w j:ℕ}{d r t t' p p':ℝ}{B:BudgetPoint}
open AnalyticBridge VerifiedReset -- conflicts.
section shore
variable {m s q:ℕ}{Y: Stars→Side} (R:∀ i:Stars,(Y i).val=2*(m*Slide.roller i.val)) (F:Stars→Type) (S:∀ i:Stars,Finset (F i))(Z:∀ i, Gem (Y i) N (F i)) (T:Finset I)(P:Gem c N I) (h:SoilB T P B w t)(hQ:∀ i,SoilB (S i) (Z i) B w t)(he:0<t)
include h he hQ
lemma trains (x: Site c)(hk:81*m≤ s)(hp:w≤q)(ht:2*s≤q): Trio.Tidy B (neighbors q x) (relic R F S Z T P x B s):=by
   let E:= relic R F S Z T P x B s; let V:= crests (cloudQ T P (B:=B)) x
   unfold relic; apply Trio.tidy_sub
   · refine Trio.tidy_sub B (u:=V) ?_ (Trio.tidy_const ..); unfold V; apply Trio.tidy_scale B; refine Trio.tidy_sum _ _ _ _ (fun i hi=>?_); unfold viewS; let p':=(Strut.act i).symm x
     have he:Trio.Tidy B (neighbors q p') (fun U=>cloudQ T P (B:=B) p' U):=by
       unfold cloudQ; refine Trio.tidy_sum B _ _ _ (fun j hj=>?_); have he' :=mem_filter.mp hj
       let H:= P.addr j; let u V:= letters P B.threshold V j; let s:= ((H.support.card:ℝ))⁻¹
       let f:=masked B.threshold H.support ((Reggae.river c N) ∘ P.view j)
       rw [show (fun v=> Reggae.river c N (u v)/ _)= (fun v=> s*f v) from funext fun v=>by unfold s u f letters; rw [Reggae.masker]; ring] -- edit
       obtain ⟨r,hp'⟩:= h.fees j he'.1; apply Trio.tidy_scale; apply Trio.tidy_mask B (AnalyticBridge.CouplingShape.reg_extend ?_ (Subset.refl _)) -- edit
       swap
       · exact (spores _ _ _ hp' (h.gauge _ he'.1) he.le).1
       exact (h.tortillas j he'.1 _ he'.2).trans (fun i hi=> (neighbors_mem ..).2 (((neighbors_mem ..).1 hi).trans hp))
     rw [← merries q x i]; exact ⟨uses_pull he.uses _ _,he.borel.comp (continuous_pull ..).measurable, invariant_pull he.invariant _ _⟩
   -- Une H.
   let p i:= crests (duskQ (S i) (Z i)); refine Trio.tidy_sum _ _ _ _ (fun i _=> Trio.tidy_scale _ _ (Trio.tidy_sum _ _ _ _ (fun j _=>?_)))
   let x':=Trio.voyageL R i j x; apply Trio.tidy_mask; swap; exact Trio.parcelH R s hk i j x ht
   apply Slide.regular (Trio.trackR R i) x' (show B.Regular univ (Boulevard.stillA (p i j)) from ?_) (fun p=> (neighbors_mem ..).2 ((village (R i).ge _ _).trans ((roll_cap m i).trans hk)))
   exact CouplingShape.reg_sub (AnalyticBridge.VerifiedReset.reg_larger (poetry (hQ i) he.le j) (subset_univ _)) (CouplingShape.reg_const _)
end shore
end YM.QCD.Grove
