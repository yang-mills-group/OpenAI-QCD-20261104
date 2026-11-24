import YM.Patria.Resp
/-! Symmetry in reading. Only origin star/equivs except translations. Use arbitrary support when tested, in real carriers even for odd. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria.Canvas
open Filter Function Set MeasureTheory Lattice Source RG Wilson Source.Drops
open scoped Matrix.Norms.Frobenius BigOperators Topology Matrix ContDiff Classical
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead
variable {B : Type*} {d k:ℕ}
open QCD.Revolve TorusPCAC.Geometry Lining Lining.Ferry Lining.Temper
open Poised Beacon Display Finset
variable (s:Signed)(H:TaperHol){c:Side}(p:EuPin)(b x:Cover)(v:ℝ)
variable (u:FlavorTorus)(Y:Density c 6)(J:Labels.Jet su)(a:Axis)(hp:p.Lifts s)(hc:18≤ c.val)
abbrev foil (P X:Density c 6)(U: Grid c): Lat.Fields c 6:= Ring.inverse (P U) * X U
variable {P:Density c 6}{L:Label d}
lemma consensus (h:Tally H b L P Y)(W:Label d)(he:Tally H b W P Y):L=W:=Subtype.ext (Beacon.chooses H b ((label_law _).1 L.property).1 ((label_law _).1 W.property).1 h.sees he.sees)
lemma moved (b₁ x: Cover)(h:Tally H x L P Y) (hg:march b₁ P=P): Tally H (x+b₁) L P (march b₁ Y):=by
    let y:= x+b₁; let V(U:Grid c):= pull 1 (wrap c b₁) U; let X:= foil P Y; let U' := foil P (march b₁ Y); let K:= crank 1 1 (wrap c b₁) (heat b₁) (N:=6)
    have hw:∀ᶠ U in 𝓝 (1:Grid c), U' U=march b₁ X U:=by
       have hf:Tendsto V (𝓝 1) (𝓝 1):=by
          have hQ : V 1=1:=by unfold V; rw [pull_one]; rfl
          exact hQ ▸ (continuous_pull ..|>.tendsto 1)
       filter_upwards [hf.eventually h.unit,h.unit] with p hp hu; have hq:= Ring.inverse_mul_eq_iff_eq_mul (P p) ((march b₁ Y) p) ((march b₁ X) p) hu; refine hq.mpr ?_; let x':=V p; change K (Y x')=P p*K (X x'); rw [show P p= _ from (congr_fun hg p).symm]; change K (Y x')= K (P x')* K (X x'); rw [← map_mul]; exact congr_arg K (Ring.mul_inverse_cancel_left (P x') (Y x') hp).symm
    refine ⟨h.unit,fun J=>?_⟩; have ht:= h.sees J
    have hf : Beacon.moment (d:=d) H y J U'=ᶠ[𝓝 0] Beacon.moment H x J X:=by filter_upwards [(centered H y J (c:=c) (d:=d)).eventually hw] with u hp; exact (congr_arg (Beacon.glow H.T y u |> fun J=> adapter J J) hp).trans (shift_seen H b₁ x u X J)
    exact ⟨ht.1.congr_of_eventuallyEq hf,ht.2.1,fun i hi=> ((hf.iteratedDeriv _).eq_of_nhds).trans (ht.2.2 _ hi)⟩
variable (Φ:Density c 6→Density c 6)(U:Label d)(B:Label d→Density c 6)(ht:Tally H 0 L P Y)
local notation "Δ"=> foil P Y
local notation "σ"=> Φ Δ
open Plans
include ht
lemma grouping (he:∀ᶠ x in 𝓝 (1:Grid c), foil P (Φ Y) x =σ x)(hV: ActionTest H 0 (B U) U.val)(hg: ActionTest H 0 (B L) L.val)(hu: Φ (B L)= B U)(ha:∀ x y,Φ (x-y)=Φ x-Φ y)(hW:∀ J:Labels.Jet su, ∃ (J': Labels.Jet su)(F: SpinPol d→L[ℝ] SpinPol d),∀ (X:Density c 6), Beacon.moment H 0 J (Φ X)=F ∘ Beacon.moment H 0 J' X): Tally H 0 U P (Φ Y):=by
    have h1 : ActionTest H 0 (Δ-B L) (0:Pol d):=by have h:= Orientation.acting H 0 d (B L) L.val hg (-1); rw [neg_one_smul,show (-1:ℂ) • (L.val:Pol d)=-L.val from neg_one_smul ℂ (L.val:Pol d)] at h; have he:= Orientation.actsPlus H 0 d Δ (-B L) L.val (-L.val) ht.sees h; rwa [add_neg_cancel, ← sub_eq_add_neg] at he
    have hT : ActionTest H 0 (Φ (Δ-B L)) (0:Pol d):= by
        intro J; obtain ⟨J',F,hF⟩:= hW J; have hx(y:Labels.Jet su) : desired (0:Pol d) y =0 := funext fun i=> by rw [← observe,map_zero]; rfl
        obtain ⟨hU,hG,hK⟩:= h1 J'; rw [hx] at hG hK; rw [hF,hx]; refine ⟨F.contDiff.contDiffAt.comp _ hU,contDiffAt_const,fun i hi=>?_⟩; rw [clm_step _ _ _ (hU.of_le (by exact_mod_cast hi)),hK _ hi,iteratedDeriv_const_zero, map_zero]
    have hp':= Orientation.actsPlus H 0 d (B U) (Φ (Δ-B L)) U.val 0 hV hT; rw [ha,hu, add_sub_cancel,add_zero] at hp' -- add_sub_cancel or add_sub_cancel_right ...
    refine ⟨ht.unit,fun J=>?_⟩; have h : Beacon.moment (d:=d) H 0 J (foil P (Φ Y)) =ᶠ[𝓝 0] Beacon.moment (d:=d) H 0 J σ:=by filter_upwards [(centered H 0 J (d:=d) (c:=c)).eventually he] with u hp; exact congr_arg _ hp
    exact ⟨(hp' J).1.congr_of_eventuallyEq h,(hp' J).2.1,fun i hi=> ((h.iteratedDeriv _).eq_of_nhds).trans ((hp' J).2.2 _ hi)⟩
-- linear motion. Using continuous maps eventually.
lemma linearT (V:Grid c → Grid c)(F: Fields c 6→ₐ[ℂ]Fields c 6) (hx: Tendsto V (𝓝 1) (𝓝 1))(hh:∀ X p, Φ X p=F (X (V p)))(hf:Φ P=P)(hV: ActionTest H 0 (B U) U.val)(hg: ActionTest H 0 (B L) L.val)(hu: Φ (B L)= B U)(hW:∀ J:Labels.Jet su, ∃ (J': Labels.Jet su)(F: SpinPol d→L[ℝ] SpinPol d),∀ (X:Density c 6), Beacon.moment H 0 J (Φ X)=F ∘ Beacon.moment H 0 J' X): Tally H 0 U P (Φ Y):=by
    apply grouping H Y Φ U B ht _ hV hg hu _ hW
    · filter_upwards [hx.eventually ht.unit, ht.unit] with p hp he; apply (Ring.inverse_mul_eq_iff_eq_mul _ _ _ he).mpr; rw [hh,hh,show P p=F (P (V p)) from (congr_fun hf p).symm.trans (hh P p),← map_mul]; exact congr_arg F (Ring.mul_inverse_cancel_left _ (Y _) hp).symm
    intro x y; funext i; rw [hh, Pi.sub_apply,Pi.sub_apply,map_sub,hh,hh]
end YM.Massive.Patria.Canvas
#print axioms YM.Massive.Patria.Canvas.linearT
