import YM.Plateau.Rock
import YM.Plateau.Phlox
/-! # Rank and the two equations. Genuine small gaps vs margin. -/
set_option autoImplicit false
noncomputable section
namespace YM.Sprig
open Function Filter Set MeasureTheory QCD.Sway
open Massive QCD QCD.Lat QCD.Grass Lattice Cylinder Patria Patria.Depth Massive.Tarn UV UV.Free
open YM.Fir Massive.Fir Choir Pollens HarmonyF YM.Intag.Sprig YM.Intag.Sprig.Canopy Chloe
open Poised Plans Plans.Stamp Poised.Stative
open scoped BigOperators Topology InnerProductSpace Classical Matrix ComplexOrder
variable {C:Sequence}{P:Calibration C}{φ:ℕ→ℕ}{Q:Choir}{d:ℕ}(T: Pollens P Q)(E: Canopy P φ Q)
variable (p q:Flavor 6)(g:Bool)
open Massive.Oriole Compass Submodule
variable {J8:Label 8→ₗ[ℂ]Label 8}{J6:Label 6→ₗ[ℂ] Label 6} (h8:Ami 8 p q g true J8)(h6:Ami 6 p q g false J6)
variable {F8: UV.Free.Symbol 8≃ₗ[ℂ](Q.level 8)}(hf8:Prose F8 T){F6: UV.Free.Symbol 6≃ₗ[ℂ](Q.level 6)}(hf6:Prose F6 T)
local notation "V"=>MassFields.isotropic
local notation "Z"=> Q.focus MassFields.isotropic 8
local notation "K"=> p
local notation "M"=> flame p q g 8 (by decide)
local notation "U"=> arbor p q g true
local notation "W₀"=> arbor p q g false
local notation "P★"=> prismT F8 M
variable (H: Q.Domestic)(hp:p≠q)
variable (C₁ L₁ R₁:Bool→ℂ)
local notation "Fc" s:arg=> Style p q g (C₁ s) (L₁ s) (R₁ s)
variable (hq:∀ s:Bool,Q.focus MassFields.isotropic 8 (Style p q g (C₁ s) (L₁ s) (R₁ s))=0)(δ:ℝ)(hδ:0 ≤δ)(ht:∀ s,‖L₁ s-parL s g‖+‖R₁ s-parR s g‖≤δ)

variable (μP:Bool→ℝ)(A ξ:ℝ)(hξ:∀ s,‖C₁ s + μP s‖ ≤ ξ)(hA:∀ s,‖(μP s:ℂ)‖ ≤ A)
include ht hq H hp h6 h8 hf8 hf6
lemma meadow (hr:δ≤1/4): let G:=Q.focus V 8 M; G≠0∧G∈ Q.level 6 ∧∀ s:Bool,∃ a:ℂ,Q.focus V 8 (arbor p q g s)=a • G:=by
      intro G; have hG:G≠0:= lineF T p q g h8 hf8 H hp C₁ L₁ R₁ hq δ ht hr; have he:= reachR T p q g H hp h8 hf8; let X:= prismT F8 M; let S:= bluff p q g true 8; have ht': Submodule.map (Q.focus V 8) S =Submodule.span ℂ ({X}:Set Q.W) := (raysW T p q g true h8 H V (by intros; rfl)).trans he;
      have hP: M∈ S:=heartL p q g H hp M (by norm_num) rfl
      obtain ⟨c,hc⟩:=mem_span_singleton.mp (show G∈span ℂ ({X}:Set Q.W) from ht' ▸ ⟨_,hP,rfl⟩)
      have h0:c≠0:=by intro h; rw[h,zero_smul] at hc; exact hG hc.symm
      have hm:=groundF T p q g h8 h6 hf8 hf6 H hp; refine ⟨hG,hc ▸ (Q.level 6).smul_mem c hm,fun s=>?_⟩
      obtain ⟨a,h⟩:=mem_span_singleton.mp (show (Q.focus V 8) (arbor p q g s)∈span ℂ ({X}:Set Q.W) from ht' ▸ ⟨arbor p q g s,(⟨flareC p q g s,fun _=>blazing p q g s⟩: _∈ S),rfl⟩)
      exact ⟨a*c⁻¹,(by rw [← hc,←h,smul_smul,mul_assoc,inv_mul_cancel₀ h0,mul_one])⟩
include hδ hξ hA
lemma signalR (hr:δ≤1/4): let F:=Q.focus V 8; F M ≠ 0∧ F M ∈ Q.level 6 ∧∃ c:ℂ,F U+F W₀ = c • F M ∧ ‖c - (μP false + poli g * μP true)‖ ≤ 2*(ξ+δ*(4*(ξ+A))):=by
    intro F; obtain ⟨hM,hP,Hq⟩:= meadow T p q g h8 h6 hf8 hf6 H hp C₁ L₁ R₁ hq δ ht hr; obtain ⟨x,hx⟩:=Hq true; obtain ⟨y,hy⟩:=Hq false; refine ⟨hM,hP,x+y,?_,?_⟩; · change Z U+Z W₀=_; rw [hx,hy,add_smul]
    have hX(s:Bool):L₁ s*x+R₁ s*y= -(C₁ s):=by
         have h:=hq s; unfold Style at h; rw [map_add,map_add,map_smul,map_smul,map_smul,hx,hy,smul_smul,smul_smul,add_assoc,←add_smul,←add_smul] at h; exact eq_neg_of_add_eq_zero_right ((smul_eq_zero.mp h).resolve_right hM) -- order
    have hE:‖x‖+‖y‖≤4*(ξ+A):=by
         have h:= smallB g L₁ R₁ δ ht (ξ+A) x y (fun s=> by rw [hX s,norm_neg]; have hh:= (norm_sub_le (C₁ s+(μP s:ℂ)) (μP s:ℂ)).trans (add_le_add (hξ s) (hA s)); rwa[add_sub_cancel_right] at hh) -- linarith no rw!
         nlinarith only[h,hr,mul_le_mul_of_nonneg_right hr (add_nonneg (norm_nonneg x) (norm_nonneg y))]
    let G(i:Bool):=parL i g*x+parR i g*y
    have hv(i:Bool): ‖G i-(μP i:ℂ)‖ ≤ ξ+δ*(4*(ξ+A)):=by
         have ht': ‖L₁ i*x+R₁ i*y-G i‖≤ δ*(‖x‖+‖y‖):=by
              unfold G; rw [add_sub_add_comm,← sub_mul,← sub_mul]; refine (norm_add_le ..).trans ?_; simp only[norm_mul]; apply le_trans _ (mul_le_mul_of_nonneg_right (ht i) (add_nonneg (norm_nonneg _) (norm_nonneg _))); rw [add_mul]; gcongr <;> first|positivity|linarith only [norm_nonneg y,norm_nonneg x]
         rw[hX,norm_sub_rev] at ht'; refine (norm_sub_le_norm_sub_add_norm_sub _ (-C₁ i) _).trans ?_; have h: ‖-C₁ i-(μP i:ℂ)‖ ≤ ξ:= by rw [← neg_add', norm_neg]; exact hξ i
         exact (add_le_add (ht'.trans (mul_le_mul_of_nonneg_left hE hδ)) h).trans_eq (add_comm ..)
    have hy: ‖y-poli g* μP true‖ ≤ ξ+δ*(4*(ξ+A)):=by
        cases g
        · refine le_trans (?_: _ ≤ ‖G true-(μP true:ℂ)‖) (hv true); dsimp [G,parR,parL,idealR,poli]; rw[zero_mul, neg_one_mul,zero_add,neg_one_mul, show -y-_ = -(y- -(μP true:ℂ)) from (by ring), norm_neg]
        simpa only [G,parR,parL,idealR,poli,↓reduceIte,zero_mul,zero_add,one_mul] using hv true
    rw [add_sub_add_comm]; refine (norm_add_le ..).trans ?_; have hx: ‖x- ↑(μP false)‖ ≤ ξ+δ*(4*(ξ+A)):=by simpa [G,parL,parR,idealR] using hv false
    exact (add_le_add hx hy).trans_eq (two_mul _).symm
end YM.Sprig
#print axioms YM.Sprig.signalR
