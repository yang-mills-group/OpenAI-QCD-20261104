import YM.Poised.Pacific
import YM.Poised.Fountain
import YM.Poised.Street
import YM.QCD.Fawn.Price
/-!
# Charter interior, picks real Crown.
Shrink discharged D.ε at furnishing before actual x height. Allows full-rank path cost with constant output.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open Function Filter Set Lattice Wilson Pressure RG Precision Tree Next Next.SectorChange Next.Fluctuations Next.Foundations
    Exterior Bloch Bid Push.SectorMeasure MultiNext.SignedSource MultiNext.SignedSource.Banjo Planned.AtomRegular MeasureTheory Analysis
open AnalyticBridge.SectorAffine.Offset WardBin.Lies PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir
open QCD QCD.Lat QCD.Kit QCD.Grass QCD.Brick QCD.Cove QCD.Stew ConnectedActivityE6.Blaze Push.Uniform UV Cylinder SourceRead
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {B :Type}[Fintype B] {c f : Side} {S : StepData c f} {T : Tube su S} {Pt : Teller su} {k : S.Choices} {V : Config su c} {F : Forest S.ratio}
    {P R : BudgetPoint} {o : Site f} {g : Site c → su.El} {X : Support f} {Y : Support c} {Q M m r t x τ W w σ G₀ ρ v s u u₁ u₂: ℝ} {I : Type} {J: BudgetPoint}
    {A : Stores S} {n l N j q₀ : ℕ} {D : Slab su c l} {q : Chi} {d : ℝ} {V' : Config su f → Lat.Fields f 6}
namespace Fountain
open Pipes
local notation "Y'"=> Fields f 6 -- remove amb
variable (a:Museum F x A X Y I)[Fintype I] {C: Libretto su n}{E: Heir.Record}
variable (hp:Plays C E P R Pt T x) (b:Cover) (hw:wrap f b∈X) (hg :Canvas P (S.ratio.parent (wrap f b)) (reach x) V g n C.C)
variable (hO:Short S R X)(hn:2≤n)(hV: Healthy P.threshold Y V) (U:Grid f)(z: Prices su I)(hu:0≤u) (hv:u*‖tape z‖≤ E.ε*R.threshold)(hl:l≤n) (hD:∀ i,P.dirBound (S.ratio.parent (wrap f b)) (D i))
set_option quotPrecheck false
local notation "L"=> S.patch.L
local notation "O"=> S.ratio.parent (wrap f b)
local notation "X₀"=> enters V (S.ratio.parent (wrap f b)) (reach x) g D (a.extra g u z)
local notation "Z₀"=> launch V (S.ratio.parent (wrap f b)) (reach x) g D
local notation "V₀"=> Heir.loom P (reach x) C.C
local notation "b'"=> Kit.slope S.patch.L
variable {p p₀ :ℕ}{I₀ I₂ χ R₁ :ℝ}
open PhysicalNext.Repeat Cub
-- ,g=1 even no Short; agreement common chart at identity.
variable [DecidableEq I](v: Directions su c)
local notation "F⚬"=> (1:Frame c)
local notation "V⚬"=> (1:Grid c)
local notation "qe"=> a.extra F⚬ u z
abbrev rod (v:Directions su c) : ℝ→L[ℝ]Directions su c:= (ContinuousLinearMap.id ℝ ℝ).smulRight v
include hp hu hv
lemma stemming : let Y(s:ℝ):=(rod v s,a.extra (1:Frame c) u z); let p(s:ℝ):= display T F x k true (Y s); let W(s:ℝ):= increment (1:Grid c) (rod v s); let q'(s:ℝ)(i:Site f):=su.lieExp (φ T F true (Y s).1 i)
    ContDiffAt ℝ n p 0∧ ∀ᶠ s in 𝓝 (0:ℝ), Agrees (inspected X) (increment (1 : Grid f) (p s)) (Lattice.gauge (q' s) (a.received k T q d u (W s) U z)):=by
    intro Y p W Q; let g:= F⚬; have hA:=hp.acts F k; have hR:= hp.rehearsed.tensions; have h₀:‖Y 0‖ ≤ loom P (reach x) C.C:=by
       unfold Y; rw [map_zero]; have he: ‖(a.extra F⚬ u z)‖ ≤ _:= (a.extra_size g u hu z).trans (hv.trans hR.noise); exact max_le ((norm_zero).le.trans ((norm_nonneg _).trans he)) he
    have hZ:ContDiff ℝ ω Y:= ((rod v).contDiff).prodMk contDiff_const
    refine ⟨(((hA.costs true).uniform _ (h₀.trans hR.allows.le)).smooth).comp _ (hZ.of_le le_top).contDiffAt,?_⟩ -- top downgrade
    filter_upwards [(hZ.continuous.continuousAt.norm.tendsto).eventually (gt_mem_nhds (h₀.trans_lt hR.allows))] with s hs
    rw [show p s=display T F x k true (Y s) from rfl,hA.represents true _ (show _ < _ from hs).le] -- hA.represents says increment .. pattern
    intro i hi hj
    let h: Museum.Station _ x (S.ratio.parent i.1):= (Corona.halo_mono (Nat.le_add_right ..) (Finset.Subset.refl _)).trans (a.asks _ hi)
    have he : AgreeNear id (S.ratio.parent i.1) (reach x) (Lattice.gauge g (W s)) (W s):=by intro i hi; exact show _ from by simp [g,Lattice.gauge]
    have ha: Lattice.gauge (g ∘ S.ratio.parent) (a.received k T q d u (W s) U z) = a.received k T q d u (W s) U z:= by ext i; simp [g,Lattice.gauge] -- ext group maybe
    exact (a.heard (k:=k) (d:=d) (q:=q) g u hp.bulletin hi hj h (by simp) true z U he).trans (congr_fun (congr_arg (Lattice.gauge (Q s)) ha) i)
-- o irrelevant b anchor.
include hn U q d
lemma hearts (p:ℝ→Directions su f)(he:p=fun s=> display T F x k true (rod v s,a.extra (1:Frame c) u z)) : (∀ i,‖p 0 i‖ ≤1) ∧ ∀ s∈Set.Icc (0:ℝ) 1,Healthy R.threshold X (increment (1:Grid f) (s • p 0)):=by
   subst p
   let p(s:ℝ):= display T F x k true (rod v s,qe)
   have h:=hp.rehearsed; have ht:= h.tensions; let l:= loom P (reach x) C.C; have hw: ‖(a.extra F⚬ u z)‖ ≤ l:= (a.extra_size F⚬ u hu z).trans (hv.trans ht.noise); let D:=E.Q*l; have hS : D≤ 1:= ht.small.trans (min_le_right ..)
   have hx:‖p 0‖≤D:=by unfold p; rw [map_zero]; exact display_price (hp.acts F k) (by omega) (max_le ((norm_zero).le.trans ((norm_nonneg _).trans hw)) hw) ht.allows.le E.majorant
   have hm(i:Bond f): ‖p 0 i‖ ≤ D:= (norm_le_pi_norm ..).trans hx
   have hp' : Healthy R.threshold X (increment (1:Grid f) (p 0)):=by
       have hW:=border_healthy hp.sew C.width C.price h.early (hp.acts F k) E.majorant hn ht a hp.bulletin C.Z (V:=V⚬) rfl h.wire hp.space h.temp_eq (one_healthy _ _ P.threshold_pos.le) (q:=q) (d:=d) U z hu hv R.threshold_pos -- order
       have h:= (stemming (k:=k) (U:=U) (d:=d) (q:=q) a hp z hu hv v).2.self_of_nhds; have he:= flags_agree R.threshold _ _ X h
       simp only [map_zero,Work.G07.at_zero_increment, gauge_flags] at he
       change Disjoint _ _ at hW ⊢; unfold p; rw [map_zero, Finset.disjoint_iff_inter_eq_empty,he]; exact Finset.disjoint_iff_inter_eq_empty.mp hW
   exact ⟨fun i=>(hm i).trans hS,(Flair.strings su).choose_spec.2 _ X _ _ (p 0) hS ((norm_nonneg _).trans hx) h.weft.squared (fun i _=>hm i) hp'⟩
end Fountain
end YM.Massive.Poised
#print axioms YM.Massive.Poised.Fountain.hearts
