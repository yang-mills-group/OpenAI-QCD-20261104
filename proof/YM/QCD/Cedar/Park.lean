import YM.QCD.Cedar.Wood

/-! # exact free match of the all-field wood -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Pine
open Lat Cost Lattice Wilson Function Finset Flume
open Laurent Bloch YM.Next.Free Metric Kit Free
open scoped Matrix.Norms.L2Operator Topology BigOperators Matrix
variable {n : Side} {j : ℕ} (P : Plan j)
lemma adjpose (X : Site n→Bundle) : star (lined X)=lined (star X):=by unfold lined; rw [ride_ad]; rfl
lemma arc_flat (i : Axis) : peel (arcL (0:Site n) 1 i)=lined fun p=> -chip (tuning p i) • 1:=by
  rw [arcL,peel_sub,peel_one,peel_shift]
  rw [lined,← show rides (Equiv.refl _) (fun _ : Site n=> (1:Bundle)) =_ from ridden, ride_sub]; congr 1; funext p
  change (1:Bundle)-cis _ • 1=(- YM.Next.Free.chip _) • (1:Bundle)
  rw [neg_smul,YM.Next.Free.chip,sub_smul,one_smul,neg_sub]; congr 2; unfold cis tuning; rw [mul_comm]
lemma wall_f (v : Train j) (a : Axis): peel (walls P (0:Site n) v 1 a)=lined fun i =>
    (plusD (tuning i) a*((P.μ:ℂ)+RRead (P.Herm v a) (tuning i)^2)) • 1:=by
  unfold walls half leaves
  simp only [peel_add,peel_smul,peel_mul,peel_star,arc_flat,deck_f _ _ (Herm_valid P v a), adjpose,lined_law]
  simp only [lined,ride_add,ride_smul]; congr 1; funext p
  simp only [Pi.add_apply, Pi.smul_apply,Pi.star_apply,Pi.mul_apply,Matrix.mul_smul,star_smul,star_one,mul_one,smul_smul]
  simp only [star_mul,star_star]; rw [P.clovely _ _ (keyboard _),star_neg,flip_chip,show star (tuning p a)=_ from congr_fun (keyboard p).1 a]
  unfold plusD; simp only [Pi.neg_apply, ← add_smul, smul_smul]; congr 1; ring
lemma veins_f (v : Train j) (a) (hj : 2≤j) : peel (skewL (vein (0:Site n) v a 1))=lined fun i=> alpha v a (tuning i) • wave (gamma a) := by
  unfold skewL vein; simp only [peel_smul,peel_sub,peel_star,peel_mul,peel_spin,deck_f _ _ (al_snap v _ hj),lined_law,adjpose]
  unfold lined; rw [ride_sub,ride_smul]; congr 1; funext i
  simp only [Pi.smul_apply,Pi.star_apply,Pi.mul_apply,Pi.sub_apply,Matrix.mul_smul,mul_one,star_smul,wave_star, gamma_star]; rw [read_al hj v a _ (keyboard i)]
  have he : star (alpha v a (tuning i)) = -(alpha v a (tuning i)):=by unfold alpha; rw [star_mul,show star _=_ from congr_fun (show star _=_ from (native_dir v _ (keyboard i).1).2) a]; simp [mul_comm]
  rw [he,neg_smul,sub_neg_eq_add, ← two_smul ℂ _]; simp [smul_smul]
lemma bare_this (n : Side) (v : Train j):wood P (0:Site n) v 1=unbarred v n:=by
  let f (a:Axis) (p:Site n):= (plusD (tuning p) a*((P.μ:ℂ)+RRead (P.Herm v a) (tuning p)^2)) • (1:Bundle)+alpha v a (tuning p) • wave (gamma a)
  apply peel_injective; rw [wood,unbarred,carries]
  have he (s : Finset Axis):peel (∑ i∈s,(walls P (0:Site n) v 1 i+skewL (vein 0 v i 1)))=lined (∑ i∈s, f i):=by
    induction s using Finset.induction_on with
    | empty=> simp [peel,lined,rides]; rfl
    | insert i s hi ih=> rw [sum_insert hi,sum_insert hi,peel_add,peel_add, ih,wall_f,veins_f v i P.good]; simp only [lined,ride_add]; rfl
  rw [he]; congr 1; funext p; unfold f rangeD Para.model Para.hiss
  rw [Finset.sum_apply,sum_add_distrib,← sum_smul,← P.certified _ _ (keyboard _),smul_sum]; congr 1; apply sum_congr rfl; intro i _; rw [smul_smul]; rfl
end YM.QCD.Pine
