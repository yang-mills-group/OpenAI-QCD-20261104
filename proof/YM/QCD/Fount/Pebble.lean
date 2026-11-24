import YM.QCD.Fount.Kev
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Fount
open Lat Kit Lattice Wilson Function Finset Filter Metric Tree RG Precision Bloch Laurent
open Orbit Flume Sparks Quarry Stationary YM.Next.Free Pine Eyrie Revolve Rudder
open Extra Iteration Placement QCD.Run Work.F08 Work.F03 Exterior Garden Leaf Tee LeafM Port
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator ContDiff Classical
variable {j k N:ℕ}{t p b C:ℝ}{P:Flight j k}{f c:Side}{e:f.val=c.val*P.L.val}
lemma pillarB (A:Plan j) : newborn c (barP P e * proton P e)=barP P e*proton P e:=by
   rw [rotateP A]; have h : (chirality f)ᴴ=chirality f:= chi_star; have he:(chirality c)ᴴ=chirality c:=chi_star; simp only [newborn,aura,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,h,he,Matrix.mul_assoc,chi_sq,Matrix.mul_one]

lemma hotS (V:Plan j)(hj:4≤j)(hk:4≤k) (h : Fractal (driftP P) t C) : dust (frosting (driftP P)) c (1:Grid c)=barP P e*proton P e:=by
   let S:=dust (driftP P) c; let T:=barP P e*proton P e; have hS : S 1=T:=rawE (A:=V) h hj hk
   have hh (s:Signed): inverted S s 1=T:= by unfold inverted; rw [show pull s 0 (1:Grid c)=1 from funext fun i=>by simp [pull,Step.read],hS]; exact icing V
   have he: hearth S 1=T:=by unfold hearth; simp_rw [hh]; rw [sum_const,card_univ,← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ (by exact_mod_cast Fintype.card_pos.ne'),one_smul]
   rw [coined_inv h]; unfold occult; rw [he, pillarB V]; module -- inspect
-- shortcuts dust eq actual
lemma lampLit {I:Type}(W:I→Bloom 0)(p:ℝ): wild W p c=dust W c:=by
   funext x; unfold wild dust; apply tsum_congr; intro i; unfold trackP Bloom.tonic; congr 1
abbrev pepperB (P:Flight j k): Fruited (Tin P 0 Unit)→Bloom 0:= frosting (driftP P)
abbrev ponder (P:Flight j k)(n:Side) := dust (pepperB P) n
lemma exultP (A:Plan j)(hj:4≤j)(hk:4≤k):∃ a C δ V:ℝ,∃ n:ℕ,0<a∧0≤ C∧ 0<δ∧0≤V∧∀ (P:Flight j k), Fractal (pepperB P) a (C*(P.L.val:ℝ))∧∀ (c f:Side)(e:f.val=c.val*P.L.val), ponder P c 1=barP P e*proton P e ∧ Own c δ 0 n (ponder P c) (V*(P.L.val:ℝ)) :=by
   obtain ⟨a,C,ha,hc,H⟩:=portend hj hk; obtain ⟨x,W,n,hx,hW,Z⟩:= LeafM.richP 0 ha (show 0≤(0:ℝ) from le_rfl)
   refine ⟨a,C,x,W*C,n,ha,hc,hx,(by positivity),fun P => ⟨?_,fun c f e=>⟨hotS A hj hk (H _),?_⟩⟩⟩
   · simpa only [ceiling,Nat.cast_zero,mul_zero,Real.exp_zero,one_mul] using! (coined a ha.le (H P) (by simp))
   unfold ponder; rw [← lampLit (pepperB P) 1]; have ht := Z _ _ _ (H P) 1 one_pos le_rfl c n le_rfl
   simpa only [one_pow,mul_one,mul_assoc] using! ht
end YM.QCD.Fount
