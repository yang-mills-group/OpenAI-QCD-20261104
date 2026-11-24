import YM.Fir.Yard
import YM.Fir.Lantern
/-! On a cofinal subsequence whole relative-position ready families persist.
No contour or sector decisions. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Fir
open YM.Fir YM.Fir.Mesh YM.Fir.NoteF Needle Needle.GaugeP Filter Set Function Metric
open Lattice Cells QCD QCD.Lat Patria Patria.Depth Patria.Hub
open UV Poised Plans Plans.Stamp Intag.Vale
open scoped Topology BigOperators Classical
variable {C:Sequence} (P:Calibration C) {β e:ℝ}(hp:C.Path β e) {n:ℕ}
variable (D:Fin n→ℕ)(u:(i:Fin n)→Label (D i))
variable (G:∀ d,Cottage P d) (hr:Sway C.S) {φ:ℕ→ℕ}
abbrev Stone d:= Fin (Module.finrank ℂ (Label d))
noncomputable def lid (d:ℕ): Module.Basis (Stone d) ℂ (Label d):= Module.finBasis ℂ (Label d)
abbrev axesZ (n:ℕ)(D:Fin n→ℕ):= (i: Fin n)→ Label (D i)
abbrev SpaceZ := (n:ℕ)→ (D:Fin n→ℕ)→ Points n → MultilinearMap ℂ (fun j=> Label (D j)) ℂ
noncomputable abbrev plain (i:ℕ)(p:Strings n):MultilinearMap ℂ (fun j=>Label (D j)) ℂ:= eyeW P D (fun _=>none) i p
structure Ability (P:Calibration C)(ψ:ℕ→ℕ)(Z:SpaceZ):Prop where
    excels n (d:Fin n→ℕ) (x:Points n)(hx:x∈conf n)(u:(i:Fin n)→ Label (d i)): Exposes C ψ (fun k p=> plain P d (ψ k) p u) x (Z n d x u)
variable {P}
noncomputable abbrev area (n:ℕ):= ((crossing n).symm)⁻¹' (conf n)
private abbrev Cup (n:ℕ):= Σ D:Fin n→ℕ, ((i:Fin n)→Stone (D i))
include hp hr G
set_option quotPrecheck false
local notation "vₐ"=>reading P
local notation "a" ψ:arg i:arg=> C.S.spacing (C.N (ψ i))
set_option maxHeartbeats 410000 in
private lemma packed (φ:ℕ→ℕ)(hφ:Tendsto φ atTop atTop) (u:(i:Fin n)→Label (D i)) (z: ↥(area n)):air _ (fun i=> looking P D u (φ i) (markF (a φ i) z.val)):=by
    have hu(k:Fin n): LightP C (vₐ D u k):=((G _).pointsP hp hr none (fun _=>u k) ⟨_,norm_nonneg (u k),Eventually.of_forall fun _=> le_rfl⟩).1
    let x:=(crossing n).symm z.val; have hh:crossing n x=z.val:= ContinuousLinearEquiv.apply_symm_apply ..; obtain ⟨B,hB,h⟩:=forest hp (vₐ D u) hr hφ x z.property hu
    let f(k:ℕ):= markF (a φ k) z.val; have hw:= visible z.val (fun _=>space0 _ _) ((tendsto_nhds_of_tendsto_nhdsWithin hp.physical).comp hφ); have he:Tendsto (fun i:ℕ=> (i,f i)) atTop (noteF (fun i=>imageF (a φ i)) (crossing n x)):=by rw [hh]; exact ride _ _ tendsto_id hw
    exact ⟨B,hB,((rouses x).comp he).eventually h⟩
private lemma makeW (φ g:ℕ→ℕ)(hv:Tendsto (φ∘g) atTop atTop)(x:Points n)(hx:x∈conf n)(R:Set ↥(area n))(hR:Dense R) (hX:∀ e∈ R,CauchySeq (fun i=>looking P D u (φ (g i)) (markF (C.S.spacing (C.N (φ (g i)))) e.val))):∃ m:ℂ,Exposes C (φ∘g) (fun k p=> plain P D (φ (g k)) p u) x m:=by
    let ψ:=φ∘g; let y: ↥(area n):= ⟨crossing n x,(show (crossing n).symm (crossing n x)∈ conf n from by rwa [ContinuousLinearEquiv.symm_apply_apply])⟩
    have hm: quiet (fun i=> a ψ i) (fun i=> looking P D u (ψ i)) y.val:= charged hp D u G hr hv x hx
    have ht:Tendsto (fun i=> a ψ i) atTop (𝓝 0):=(tendsto_nhds_of_tendsto_nhdsWithin hp.physical).comp hv
    obtain ⟨m,hh⟩:= Quiet.dense (fun _=>space0 _ _) ht y hm hR hX
    refine ⟨m,(nNote x ..).mpr ?_⟩; exact hh
private lemma crest (φ:ℕ→ℕ)(hφ:Tendsto φ atTop atTop):∃ g:ℕ→ℕ,StrictMono g∧∀ (n:ℕ)(p:Cup n)(x:Points n),x∈conf n →∃ c:ℂ,Exposes C (φ ∘ g) (fun k b=>plain P p.1 (φ (g k)) b (fun i=> lid (p.1 i) (p.2 i))) x c:=by
    choose R ht hR using fun n=> TopologicalSpace.exists_countable_dense (area n) -- syntax
    let I:= Σ n:ℕ,Cup n × (R n); let J (i:I):=i.2.1.1; let U(i:I)(j:Fin i.1):= lid (J i j) (i.2.1.2 j); let R' i:= ((i:I).2.2).val.val
    let F(i:I)(k):= looking P (J i) (U i) (φ k) (markF (a φ k) (R' i))
    haveI (n:ℕ): Countable (R n):= (ht n).to_subtype -- ok?
    haveI : Countable I:=by unfold I Cup; infer_instance
    obtain ⟨g,hg,f,hf⟩:= Lantern.armor (W:=fun _=>ℂ) F (fun i=>by
         exact packed hp (J i) G hr φ hφ _ ((i.2.2).val))
    refine ⟨g,hg,fun n p x hx=> makeW hp p.1 _ G hr φ g (hφ.comp hg.tendsto_atTop) x hx (R n) (hR n) (fun e he=>?_ )⟩; exact Filter.Tendsto.cauchySeq (hf ⟨n,p,⟨e,he⟩⟩) -- name
lemma year (φ:ℕ→ℕ)(hφ:Tendsto φ atTop atTop): ∃ g:ℕ→ℕ,StrictMono g ∧∃ Z:SpaceZ,Ability P (φ∘g) Z:=by
    obtain ⟨g,hg,h⟩:= crest hp G hr φ hφ
    choose! X hX using h
    let Z: SpaceZ:=fun n d x=> YM.Multilabel.ofBasis (fun i=> lid (d i)) (fun v' => X n ⟨d,v'⟩ x)
    refine ⟨g,hg,Z, ⟨fun n d x hx p=>?_⟩⟩; refine Lantern.horizons (fun i=>lid (d i)) _ (Z n d x) ?_ _ _ tendsto_const_nhds; intro v'
    unfold Z; rw [YM.Multilabel.applyBasis]; exact hX n ⟨d,v'⟩ x hx
-- project Varying labels
omit hp hr G
namespace Ability
variable {Z:SpaceZ} {ψ:ℕ→ℕ}(H:Ability P ψ Z)
include H
lemma turns (w:ℕ→ axesZ n D)(h:Tendsto w atTop (𝓝 u))(x:Points n)(hx:x∈conf n):Exposes C ψ (fun k p=> plain P D (ψ k) p (w k)) x (Z n D x u):= Lantern.horizons (fun i=> lid (D i)) _ _ (fun j=> H.excels n D x hx _) _ _ (h.comp beyond)
end Ability
end YM.Massive.Fir
#print axioms YM.Massive.Fir.year
#print axioms YM.Massive.Fir.Ability.turns
