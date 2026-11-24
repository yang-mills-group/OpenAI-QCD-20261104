import YM.QCD.Revolve.Pin
import YM.QCD.Revolve.Shade
import YM.QCD.Step.Tour

/-! # Twisted hypercube motion -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Revolve
open Lat Lattice Function Finset Wilson Kit
open scoped Matrix Matrix.Norms.L2Operator BigOperators
variable {n : Side} {s : Signed} {b t t' : Site n} {l : Site n→ℂ} {P : Spike} (h : Glare s t t' b l) (hp : Swing s P)

def shiftE (s : Signed) (b : Site n) : Equiv.Perm (Site n) := s.actEquiv.toEquiv.trans (Equiv.addRight b)
def hues (b : Site n) (s : Signed) (l : Site n→ℂ) (P : Spike) := rides (shiftE s b) fun i=> l i • wave (star P)
lemma wave_neg (Q : Spike) : wave (-Q)=-(wave Q):=kron_neg ..
lemma wobble (Q : Spike) (H : Q∈unitary _) : wave Q ∈ unitary _:=
  ⟨by rw [wave_star,wave_mul,H.1,wave_one],by rw [wave_star,wave_mul,H.2,wave_one]⟩
include h hp
lemma colour_wheel : hues b s l P∈unitary _:=by
  have H:=wobble _ (Unitary.star_mem hp.unit)
  unfold hues; refine unitary_ride _ (fun i=>?_)
  rcases h.sign i with he|he
  · rw [he,one_smul]; exact H
  rw [he,neg_smul,one_smul]; constructor <;> simp only [star_neg,neg_mul_neg] <;> first | exact H.1 | exact H.2
omit h hp

def hitch (t : Site n) (U : Grid n) (a : Step) (x : Site n):= glint t x a • colour (a.read U x)
lemma leg_day (t : Site n) (U : Grid n) (a : Step) : leg t U a=rides (Equiv.addRight a.vec) fun i=>touch (hitch t U a i):=by
  rcases a with ⟨a,_|_⟩; · rfl
  unfold leg; rw [if_pos rfl,opp]
  congr 1
  · ext1; simp [back,Equiv.addRight,Step.vec,sub_eq_add_neg]
  funext i; unfold hitch thread; rw [star_smul,seam_real]; congr 2

include h
lemma turned_leg (P : Spike) (U : Grid n) (a : Step) : leg t (pull s b U) a*hues b s l P=hues b s l P*leg t' U (a.rotate s):=by
  rw [leg_day,leg_day,hues,ride_mul,ride_mul]; congr 1
  · ext1 i; exact affine_add s b i a
  funext i; unfold hitch; rw [Step.pull_read]; simp only [touch,Matrix.kronecker_smul, Matrix.smul_mul,Matrix.mul_smul,smul_smul]
  congr 1
  · rw [mul_comm (l _),mul_comm _ (l i)]; exact glared h a i
  exact (interlace _ _).eq
include hp
lemma hue_path (U : Grid n) (w : Walk): routeM t (pull s b U) w=hues b s l P*routeM t' U (w.map (·.rotate s))*star (hues b s l P):=by
  have he : routeM t (pull s b U) w*hues b s l P=hues b s l P*routeM t' U (w.map (·.rotate s)):=by
    induction w with
    | nil=> simp [routeM]
    | cons a w ih=>
      change leg t _ _*routeM t (pull s b U) w*hues b s l P=_; rw [mul_assoc,ih,← mul_assoc,turned_leg h,mul_assoc]; rfl
  rw [← he, mul_assoc,(colour_wheel h hp).2,mul_one]
lemma hue_march (U : Grid n) (a : Axis): shift t (pull s b U) a=hues b s l P*(if s.flip a then star (shift t' U (s.perm a)) else shift t' U (s.perm a))*star (hues b s l P):=by
  have H:=hue_path h hp U [posDir a]; simp only [routeM,List.map_cons,List.prod_cons,List.map_nil,List.prod_nil,mul_one] at H
  simpa only [leg,posDir, Step.rotate,Bool.false_eq_true, ↓reduceIte,Bool.false_xor] using H
lemma hue_gamma (a:Axis): onSpin n (gamma a)=hues b s l P*(if s.flip a then -onSpin n (gamma (s.perm a)) else onSpin n (gamma (s.perm a)))*star (hues b s l P) := by
  have he : onSpin n (gamma a)*hues b s l P=hues b s l P*(if s.flip a then -onSpin n (gamma (s.perm a)) else onSpin n (gamma (s.perm a))):=by
    have hh : star (P*gamma a)=star ((if s.flip a then -gamma (s.perm a) else gamma (s.perm a))*P):= congr_arg star (hp.sends a)
    split_ifs with h
    · unfold onSpin hues; rw [mul_neg,ride_mul,ride_mul,Equiv.refl_trans,Equiv.trans_refl]; rw [← neg_one_smul ℂ,ride_smul]; congr 1; funext x; dsimp only [Pi.smul_apply]; simp only [Equiv.refl_apply,Matrix.mul_smul,Matrix.smul_mul,wave_mul,neg_one_smul]
      rw [if_pos h,star_mul,star_mul,gamma_star,star_neg,gamma_star, mul_neg] at hh; rw [hh,wave_neg,smul_neg]
    unfold onSpin hues; rw [ride_mul,ride_mul,Equiv.refl_trans,Equiv.trans_refl]; congr 1; funext x; simp only [Equiv.refl_apply,Matrix.mul_smul,Matrix.smul_mul,wave_mul]; rw [if_neg h,star_mul,star_mul,gamma_star,gamma_star] at hh; rw [hh]
  rw [← he, mul_assoc, (colour_wheel h hp).2,mul_one]
end YM.QCD.Revolve
