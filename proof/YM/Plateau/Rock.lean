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
private lemma quPaux(x:Spike)(hx:x∈ unitary Spike):x≠0:=fun h=>by rw [h] at hx; have hp:=hx.2; simp at hp
lemma quPul : pulp g≠0:= quPaux _ (P_high _)
include H hf8 hp h8
lemma locL : prismT F8 M≠0:=by intro h; have h': F8 (projection M)=0:= Subtype.ext h; rw [map_eq_zero_iff _ F8.injective] at h'; exact UV.Free.Harbor.meson_visible p q (pulp g) (d:=8) (by omega) (quPul g) h'
-- Rank across. 
include h6 hf6
lemma groundF : prismT F8 M ∈ Q.level 6:=by
    let v:= flame p q g 6 (by decide); let x:= Q.focus none 6 v; have hP:x≠0:=rate6 T p q g H none h6 hp hf6 _ (quPul g); have hx:x∈lensP T p q g true⊓Q.level 8:=by
         have ht: x∈Q.level 6:=⟨v,rfl⟩; refine ⟨?_,H.slope (by norm_num:6≤8) ht⟩
         intro i; have he:= (gateL p q g true P.sym v).mp (heartL p q g H hp _ le_rfl rfl) i; rcases i with j|j;
         · change T.flavor j (Q.focus none 6 v)=_; rw [T.f,show P.sym.flavor 6 j v=_ from he,map_smul]
         change T.spin j.1.val.1 (Q.focus none 6 v)=_; rw [T.w _ _ j.1.prop.1,show P.sym.pin 6 j.1.val.1 v=_ from he,map_smul]; rfl
    rw [reachR T p q g H hp h8 hf8] at hx; obtain ⟨c,hc⟩:= Submodule.mem_span_singleton.mp hx; have hh:c≠0:=fun h=>by rw[h,zero_smul] at hc; exact hP hc.symm
    rw[← inv_smul_smul₀ hh (prismT F8 M),hc]; exact Submodule.smul_mem _ _ (⟨v,rfl⟩:x∈Q.level 6)
variable (C₁ L₁ R₁:Bool→ℂ)
local notation "Fc" s:arg=> Style p q g (C₁ s) (L₁ s) (R₁ s)
variable (hq:∀ s:Bool,Q.focus MassFields.isotropic 8 (Style p q g (C₁ s) (L₁ s) (R₁ s))=0)(δ:ℝ)(hδ:0 ≤δ)(ht:∀ s,‖L₁ s-parL s g‖+‖R₁ s-parR s g‖≤δ)
-- generic scalar lemma
omit H hf8 hp h6 h8 hf6
include ht
lemma smallB (A: ℝ)(x y:ℂ)(h:∀ s:Bool,‖L₁ s*x+R₁ s*y‖ ≤ A):‖x‖+‖y‖ ≤2*A+ 2*δ*(‖x‖+‖y‖):=by
       let f(s:Bool):ℂ:= parL s g*x+parR s g*y
       have he(s:Bool): ‖f s‖ ≤ A+δ*(‖x‖+‖y‖):=by
            let Fh(s:Bool):ℂ:=L₁ s*x+R₁ s*y
            have hQ:‖Fh s-f s‖ ≤ δ*(‖x‖+‖y‖):=by
                 unfold f Fh; rw [add_sub_add_comm,←sub_mul,←sub_mul]; refine (norm_add_le ..).trans ?_; simp only[norm_mul]; apply le_trans _ (mul_le_mul_of_nonneg_right (ht s) (add_nonneg (norm_nonneg _) (norm_nonneg _))); rw [add_mul]; gcongr <;> first|positivity|linarith only [norm_nonneg y,norm_nonneg x]
            exact le_trans (by nth_rw 1 [show f s= Fh s-(Fh s-f s) from (by ring)]; exact norm_sub_le (Fh s) _) (add_le_add (h s) hQ) -- rw duplicates
       have hX: ‖f false‖=‖x‖:=by simp [f,parL,parR,idealR]
       have hY: ‖f true‖=‖y‖:=by cases g<;>simp[f,poli,parL,parR,idealR]
       linarith only [hX,hY,he true,he false]
omit ht
lemma worthM(x y z:ℂ):Style p q g x y z∈ bluff p q g true 8:=by
       let T:=bluff p q g true 8; have h(t:Bool):arbor p q g t∈ T:= ⟨flareC p q g t,fun _=> blazing p q g t⟩; exact T.add_mem (T.add_mem (T.smul_mem _ (⟨charm p q 0 0 _,fun _=> blitheP p q g (0:Multi 8) 0⟩: (flame p q g 8 (by decide))∈ T)) (T.smul_mem _ (h _))) (T.smul_mem _ (h _))
include H hf8 hp h8 ht hq
local notation "Uκ" => lensP T p q g true
lemma lineF (hr:δ ≤ 1/4): Q.focus MassFields.isotropic 8 M≠0:=by
       let X:= prismT F8 M; let K1:= (bluff p q g true 8); have h : K1.map (Z)= (Uκ)⊓ Q.level 8 := raysW T p q g true h8 H V (by intros; rfl)
       have hR(s:Bool): Z (arbor p q g s) ∈ Submodule.span ℂ ({X}:Set Q.W):= (reachR T p q g H hp h8 hf8) ▸ (show _∈(Uκ)⊓ Q.level 8 from h ▸ ⟨_,(⟨flareC p q g s,fun _=>blazing p q g s⟩:arbor p q g s∈K1),rfl⟩)
       obtain ⟨α,hα⟩:=mem_span_singleton.mp (hR true); obtain ⟨β,hβ⟩:=mem_span_singleton.mp (hR false); intro hh
       have hz(s:Bool): L₁ s*α+R₁ s*β=0:=by
            have h:= hq s; unfold Style at h; rw [map_add,map_add,map_smul,map_smul,map_smul,hh,smul_zero,zero_add,← hα,←hβ,smul_smul,smul_smul,←add_smul] at h; exact (smul_eq_zero.mp h).resolve_right (locL T p q g h8 hf8 H hp)
       have hP:= smallB g L₁ R₁ δ ht 0 α β (fun i=> by rw[hz,norm_zero]); obtain ⟨h1,h2⟩ : α=0 ∧ β=0:= by
            rw[← norm_le_zero_iff, ← norm_le_zero_iff]; have ht': 0≤‖α‖+‖β‖:=by positivity
            constructor <;> nlinarith only [hr,hP,norm_nonneg α,norm_nonneg β, mul_le_mul_of_nonneg_right hr ht']
       obtain ⟨z,hx,hg⟩:= (show X∈ K1.map Z from (h.trans (reachR T p q g H hp h8 hf8)).symm ▸ (Submodule.mem_span_singleton_self X)); obtain ⟨v,y,w,rfl⟩:= Massive.Oriole.rose p q g z hp hx.1 (hx.2 rfl)
       rw [map_add,map_add,map_smul,map_smul,map_smul,hh,←hα,←hβ,h1,h2,zero_smul,smul_zero,smul_zero,smul_zero,add_zero,add_zero] at hg; exact locL T p q g h8 hf8 H hp hg.symm
end YM.Sprig
#print axioms YM.Sprig.groundF
#print axioms YM.Sprig.worthM
#print axioms YM.Sprig.lineF
