import YM.Pods.Spy
/-! Single reflection comparison in Chess.F.copy.Patric.E actual density orientation. Only up to sign for parity-homogeneous field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive
open Function Filter Set Lattice Wilson RG MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius TensorProduct Classical ComplexConjugate Kronecker Matrix
namespace Romance
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead QCD.Revolve Tide
open TorusPCAC.Geometry Chess Patria Patria.Exposure Cells QCD.RP
variable {i j k d N n:ℕ}{c f:Side}
variable (C: Regulator c 6) (T: Cells.Cut c) (b:Cover)
local notation "s" => T.flip
local notation "N₀"=>T.slide
local notation "a₀"=>T.pos
local notation "i₀"=>wrap c b
local notation "P₀"=>heat (n:=c) b
local notation "M"=>hues i₀ 1 P₀ 1
local notation "F"=>hues (0:Site c) s (prism s) (gamma T.pos)
local notation "Ω"=>Tide.lens T
local notation "cP"=>Lat.copies 6
local notation "G"=>eyeP c T.pos
lemma sign_glare {u v:Site c→ℂ} {x:Site c} {R:Signed} (hu:Glare R 0 0 x u)(hv:Glare R 0 0 x v) : SignedEq u v:=by
    have h(i:Site c):u 0*v i=v 0*u i:=by
         obtain ⟨w,hw⟩:= tracks (0:Site c) i; have h₁:=flare_path hu w 0; have h₂:= flare_path hv w 0; rw [hw] at h₁ h₂; let s':= shimmer 0 (0:Site c) w; apply mul_left_cancel₀ (shimmer_ok (0:Site c) w); rw [mul_left_comm, h₂,mul_left_comm _ (v 0) (u i),h₁,mul_left_comm]
    rcases hu.sign 0 with hx|hx <;> rcases hv.sign 0 with hg|hg <;> simp only [hx,hg,one_mul,neg_one_mul] at h
    · exact Or.inl (funext fun i=> (h i).symm)
    · exact Or.inr (funext fun i=> neg_eq_iff_eq_neg.mp (h i).symm)
    · exact Or.inr (funext fun i=> (h i).symm)
    exact Or.inl (funext fun i=> neg_inj.mp (h i).symm)
variable (ht:wrap c b=T.slide) (hv:T.kind=.link) -- macro warning change
local notation "Pσ" =>fun i:Site c=> prism s i* heat b (affine s 0 i)
include ht hv
lemma lensχ : SignedEq (F*M) Ω:=by
    have hu: Glare (T.flip) 0 (0:Site c) T.slide Pσ:=by have h:= via_glare (smoke (c:=c) s) (glares (n:=c) b); rw [one_mul,affine,ht,Signed.act_zero,zero_add] at h; exact h
    have hp : F*M=hues T.slide T.flip Pσ (gamma T.pos):=by
        unfold hues; rw [ride_mul]; have hx:(shiftE s (0:Site c)).trans (shiftE 1 (wrap c b)) = shiftE s T.slide:= Equiv.ext fun i=>by change affine 1 _ (affine s 0 i)= affine s _ i; rw [ht]; simp [affine] -- affine order.V
        rw [hx]; congr 1; funext i; simp only [star_one,wave_one,Equiv.trans_apply]; rw [Matrix.smul_mul, Matrix.mul_smul, mul_one,mul_smul]; rfl
    rw [hp]; unfold Tide.lens; rcases sign_glare hu (glances T hv) with h|h; · rw [show (Pσ)= _ from h]
    apply Or.inr; unfold hues; rw [show (Pσ)= _ from h]; rw [← neg_one_smul ℂ (rides _ _),ride_smul]; congr 1; funext i; simp
omit hv
lemma rotated_pull (V:Grid c): pull (Signed.mirror T.pos) (0:Site c) (pull 1 i₀ V)= T.pullC su V:=by rw [pull_pull, one_mul]; unfold Cut.pullC; rw [ht]; simp [affine]
omit ht
-- every parity insertion E' move by translation.A.Trans conduct.
variable (x:Insertion c 6)(V:Grid c)
local notation "G'"=>cP Ω
variable (hc:C.t=0)
local notation "R"=>C.zeroCut
include ht hv
lemma ticket (V:Grid c) : Patria.march b (Action.adj a₀ ⇑x) V = adapter (cP (-(F*M))) (Twist (cP (-(F*M)))) (QCD.Grass.turn (x (T.pullC su V))):=by
    unfold Patria.march post crank; rw [eye_value, rotated_pull T b ht]; unfold QCD.Kit.disguise; rw [tilts]; let Z:= G; have he: cP F = eyeP c T.pos:=by rw [rotor,gamma_star] -- star gamma.Scope amb
    have hh : ((-G)ᵀ)=Twist (-G):=by unfold Twist; rw [← Matrix.star_eq_conjTranspose,star_neg,eye_star]
    rw [hh,adapt_together, show (star (cP M))ᵀ=Twist (cP M) from rfl, ← Grass.twist_mul,← he, ← RP.copies_neg,← copies_mul]; rw [neg_mul] -- finish replace
include hc
lemma pic_match (q:Bool)(hx:∀ V, QCD.Grass.Hom q (x V)) : SignedEq ⇑(picture T R x) (Patria.march b (Action.adj a₀ ⇑x)):=by
    rcases lensχ T b ht hv with h|h
    · exact Or.inl (funext fun V=>by rw [one_grading R x T hc,ticket T b ht hv x,h])
    have hr (V:Grid c): grade (picture T R x V)=(Patria.march b (Action.adj a₀ ⇑x)) V:=by
          rw [one_grading R x T hc,ticket T b ht hv x,h,neg_neg]; rw [← adapter_neg,adapt_together,RP.copies_neg]; simp only [mul_neg_one,neg_neg]; unfold Twist; simp
    have he (V:Grid c): Grass.Hom q (picture T R x V):= by
         obtain hp:= hx (T.pullC su V); rw [paints R x T hc]; cases q <;> simp only [Grass.Hom,Plus,Minus,Bool.false_eq_true,↓reduceIte] at hp ⊢ <;> rw [tilt_grade,hp]; exact map_neg ..
    cases q; · exact Or.inl (funext fun i=> (show (picture T R x) i= _ from (show grade _ = _ from he i).symm).trans (hr i)) -- implicit issues
    exact Or.inr (funext fun i=> (neg_eq_iff_eq_neg).mp ((he i).symm.trans (hr i)))
end Romance
end YM.Massive
#print axioms YM.Massive.Romance.pic_match
