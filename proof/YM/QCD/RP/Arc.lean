import YM.QCD.RP.Positive

/-!
# Move the fermionic seam

Scalar ±1 substitution on both ψ and bar. Arc closed at the start. Exact on insertions,
not just determinants.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.RP
open Lattice Wilson Grass Lat Function Finset
open scoped BigOperators Matrix.Norms.Frobenius Matrix Topology

variable {n : Side} {F : ℕ} {R : Cells.Cut n}

-- Site gauge sign, only needed along one axis at a time.
structure Tape (n : Side) where
  a : Axis
  start : Per n
  stop : Per n

namespace Tape
variable (T : Tape n)

def stamp (x : Site n) : ℂ := if (x T.a-T.start).val < (T.stop - T.start).val then -1 else 1
lemma sign (x) : T.stamp x=1 ∨ T.stamp x=-1 := by unfold stamp; split <;> tauto
@[simp] lemma squared (x) : T.stamp x*T.stamp x=1 := by rcases T.sign x with h|h <;> rw [h] <;> simp
@[simp] lemma real (x) : star (T.stamp x)=T.stamp x := by rcases T.sign x with h|h <;> rw [h] <;> simp
@[simp] lemma norm (x) : ‖T.stamp x‖=1 := by rcases T.sign x with h|h <;> rw [h] <;> simp

lemma steady (t : Site n) (hs : T.start=t T.a) (x : Site n) : T.stamp x*seam t x T.a*T.stamp (x+step T.a)=
    seam (Function.update t T.a T.stop) x T.a := by
  let i := (x T.a-T.start).val
  let d := (T.stop-T.start).val
  have hi : (i:Per n)=x T.a-T.start := ZMod.natCast_zmod_val _
  have hv : i < n.val := ZMod.val_lt _
  have hd : (d:Per n)=T.stop-T.start := ZMod.natCast_zmod_val _
  have hz : d < n.val := ZMod.val_lt _
  unfold stamp seam
  simp only [Pi.add_apply,step_apply,if_true, update_self,← hs]
  change (if i<d then _ else _)*(if x T.a+1=T.start then _ else _)*(if (x T.a+1-T.start).val<d then _ else _)=_
  have hg : x T.a+1-T.start=((i+1:ℕ):Per n) := by push_cast; rw [hi]; ring
  have hr : x T.a+1=T.start ↔ (x T.a+1-T.start).val=0 := by simp [sub_eq_zero]
  have ht : x T.a+1=T.stop ↔ (x T.a+1-T.start).val=d := by
    constructor
    · intro h; rw [h]
    intro h; rw [← sub_left_inj (a:=T.start)] -- check
    apply ZMod.val_injective n.val h
  by_cases he : i+1=n.val
  · simp only [hr,ht,hg,he,ZMod.natCast_self,ZMod.val_zero]
    have hb : ¬ i<d := by omega
    by_cases h : d=0
    · simp [h]
    simp [hb,Ne.symm h,Nat.pos_of_ne_zero h]
  simp only [hr,ht,hg,ZMod.val_natCast_of_lt (show i+1<n.val from by omega)]
  split_ifs <;> first | omega | norm_num
  all_goals contradiction

lemma stamps (t : Site n) (hs : T.start=t T.a) (x : Site n) (a) :
    T.stamp x*seam t x a*T.stamp (x+step a)=seam (Function.update t T.a T.stop) x a := by
  by_cases H : a=T.a
  · subst a; exact T.steady t hs x
  have hh : seam (Function.update t T.a T.stop) x a=seam t x a := by simp [seam,H]
  have he : T.stamp (x+step a)=T.stamp x := by simp [stamp,Ne.symm H]
  rw [he,hh,mul_right_comm,T.squared,one_mul]

def tag : Sheet n := Matrix.diagonal (fun i => T.stamp i.1)
lemma tags : T.tag=rides (Equiv.refl _) (fun x => (T.stamp x) • (1:Bundle)) := by ext ⟨i,j⟩ ⟨k,l⟩; by_cases h : i=k <;> by_cases hz : j=l <;> simp [tag,h,hz,rides,Matrix.one_apply]
lemma tag_star : star T.tag=T.tag := by
  ext i j; by_cases h : i=j; · simp [h,tag]
  simp [h,Ne.symm h,tag]
lemma tag_sq : T.tag*T.tag=1 := by rw [tag,Matrix.diagonal_mul_diagonal]; simp_rw [T.squared]; exact Matrix.diagonal_one
lemma tag_trans : T.tagᵀ=T.tag := Matrix.diagonal_transpose _
lemma tag_roll (k : Frame n) : T.tag*siteRot k=siteRot k*T.tag := by rw [tags,siteRot,ride_mul,ride_mul]; simp only [Equiv.refl_apply, Matrix.mul_smul,Matrix.smul_mul,one_mul,mul_one]
lemma tag_spin (A : Spike) : T.tag*onSpin n A=onSpin n A*T.tag := by rw [tags,onSpin,ride_mul,ride_mul]; simp only [Equiv.refl_apply, Matrix.mul_smul,Matrix.smul_mul,one_mul,mul_one]

lemma covered (t : Site n) (hs : T.start=t T.a) (U : Grid n) (a : Axis) :
    shift (Function.update t T.a T.stop) U a = T.tag * shift t U a * T.tag := by
  unfold shift; rw [tags,ride_mul,ride_mul,Equiv.refl_trans,Equiv.trans_refl]; congr 1; funext x
  simp only [thread,← T.stamps t hs x,Matrix.smul_mul,Equiv.refl_apply,Matrix.one_mul, Matrix.mul_smul,Matrix.mul_one,hop]
  ext ⟨_,_⟩ ⟨_,_⟩; simp only [touch,Matrix.smul_apply,Matrix.kroneckerMap_apply,smul_eq_mul]; ring
lemma cover_adj (t : Site n) (hs : T.start=t T.a) (U : Grid n) (a : Axis) :
    star (shift (Function.update t T.a T.stop) U a) = T.tag * star (shift t U a) * T.tag := by rw [covered _ _ hs,star_mul,star_mul,T.tag_star,mul_assoc]
lemma cover_hop (t : Site n) (hs : T.start=t T.a) (U : Grid n) (a) :
    singleHop (Function.update t T.a T.stop) U a=T.tag*singleHop t U a*T.tag := by
  unfold singleHop; rw [cover_adj _ _ hs,covered _ t hs,mul_add,add_mul]; congr 1 <;> rw [← mul_assoc, ← mul_assoc,← tag_spin, mul_assoc T.tag]
lemma cover_basis (t : Site n) (hs : T.start=t T.a) (U : Grid n) (m : ℝ) :
    bareD (Function.update t T.a T.stop) U m=T.tag*bareD t U m*T.tag := by
  unfold bareD; rw [mul_add,add_mul]; simp only [Matrix.mul_sum,Matrix.sum_mul,Matrix.mul_smul,Matrix.smul_mul,mul_sub,sub_mul,
    mul_one,T.tag_sq,T.cover_hop t hs]

def bands (F : ℕ) := Matrix.diagonal (fun i : Modes n F => T.stamp i.1.1)
lemma band_copies (F) : T.bands F=copies F T.tag := by ext ⟨i,j⟩ ⟨k,l⟩; by_cases h : i=k <;> by_cases hc : j=l <;> simp [bands,tag,copies,h,hc,Matrix.blockDiagonal_apply]
lemma band_trans (F) : (T.bands F)ᵀ=T.bands F := Matrix.diagonal_transpose _
lemma band_star (F) : star (T.bands F)=T.bands F := by rw [band_copies,← copies_star,T.tag_star]
lemma band_sq (F) : T.bands F*T.bands F=1 := by rw [band_copies,← copies_mul,T.tag_sq,copies_one]
lemma band_rot (F) (k : Frame n) : T.bands F*rotates F k=rotates F k*T.bands F := by unfold rotates; rw [band_copies,← copies_mul,← copies_mul,tag_roll]

def tape (F : ℕ) : Fields n F →ₐ[ℂ] Fields n F := adapter (T.bands F) (T.bands F)
lemma rolled (x : Fields n F) : T.tape F (T.tape F x)=x := by simp only [tape,adapt_together,band_sq,adapt_one]
lemma tape_amp (x : Fields n F) : ber _ (T.tape F x)=ber _ x := by rw [tape,volume_map, ← Matrix.det_mul,band_sq, Matrix.det_one,one_mul]
lemma tape_slot (x : Fields n F) (k : Frame n) : T.tape F (slots F k x)=slots F k (T.tape F x) := by
  have he := congrArg Twist (band_rot T F k)
  have hv : Twist (T.bands F) = T.bands F := by unfold Twist; rw [← Matrix.star_eq_conjTranspose,band_star,band_trans]
  rw [twist_mul,twist_mul,hv] at he
  rw [tape,slots,adapt_together,adapt_together,band_rot]
  rw [show (star (rotates F k))ᵀ * T.bands F=T.bands F*(star (rotates F k))ᵀ from he.symm]
@[simp] lemma tape_psi (i : Modes n F) : T.tape F (psi i)=T.stamp i.1.1 • psi i := by rw [tape,adapt_psi]; simp [bands,Matrix.diagonal_apply,ite_smul]
@[simp] lemma tape_bar (i : Modes n F) : T.tape F (bar i)=T.stamp i.1.1 • bar i := by rw [tape,adapt_bar]; simp [bands,Matrix.diagonal_apply,ite_smul]

def swap (C : Lat.Cut n F) : Lat.Cut n F := { C with t := Function.update C.t T.a T.stop }
lemma flexes (C : Lat.Cut n F) (h : T.start=C.t T.a) (U : Grid n) :
    (T.swap C).insertD U=T.tape F (C.insertD U) := by
  rw [swap,Lat.Cut.insertD_apply,Lat.Cut.insertD_apply,tape,gauss_map,T.band_trans,Lat.Cut.ferm]
  rw [T.band_copies]; dsimp only; rw [T.cover_basis C.t h,copies_mul,copies_mul,mul_assoc]; rfl

def roll (x : Insertion n F) : Insertion n F :=
  ⟨fun U => T.tape F (x U), (T.tape F).toLinearMap.continuous_of_finiteDimensional.comp x.continuous⟩
@[simp] lemma rolls (x : Insertion n F) (U) : T.roll x U=T.tape F (x U) := rfl
lemma unroll (x : Insertion n F) : T.roll (T.roll x) = x := by ext1 U; simp [T.rolled]
lemma roll_grade (x : Fields n F) : grade (T.tape F x)=T.tape F (grade x) := exterior_parity ..
lemma roll_invariant (x : Insertion n F) (h : Invariant x) : Invariant (T.roll x) := by
  intro k; ext1 U
  change slots F k (T.tape F (x (gauge k U)))=T.tape F (x U)
  rw [← tape_slot,show slots F k (x (gauge k U))= x U from congrArg (fun f : Insertion n F => f U) (h k)]
lemma roll_one : T.roll (1 : Insertion n F)=1 := by ext1 U; exact map_one (T.tape F)
lemma roll_mul (x y : Insertion n F) : T.roll (x*y)=T.roll x * T.roll y := by ext1 U; exact map_mul (T.tape F) _ _
lemma rolls_rate (C : Lat.Cut n F) (h : T.start=C.t T.a) (x : Insertion n F) (U) : (T.swap C).rate (T.roll x) U = C.rate x U := by
  unfold Lat.Cut.rate; simp only [ContinuousMap.mul_apply,T.flexes C h,rolls,← map_mul,T.tape_amp]; rfl
lemma roll_raw (C : Lat.Cut n F) (h : T.start=C.t T.a) (x : Insertion n F) : (T.swap C).raw (T.roll x)=C.raw x := by
  unfold Lat.Cut.raw; dsimp only [LinearMap.coe_mk,AddHom.coe_mk]; simp_rw [T.rolls_rate C h]
lemma roll_normer (C : Lat.Cut n F) (h : T.start=C.t T.a) : (T.swap C).partitionR=C.partitionR := by
  unfold Lat.Cut.partitionR; rw [← roll_raw T C h, T.roll_one]
lemma roll_average (C : Lat.Cut n F) (h : T.start=C.t T.a) (x : Insertion n F) : (T.swap C).average (T.roll x)=C.average x := by simp only [Lat.Cut.average,LinearMap.smul_apply,T.roll_raw C h,T.roll_normer C h]
end Tape

def mount (R : Cells.Cut n) (C : Lat.Cut n F) : Tape n := ⟨R.pos,C.t R.pos,Slice.Link.top R+1⟩
lemma tuned (R : Cells.Cut n) (C : Lat.Cut n F) : Matches ((mount R C).swap C) R := Function.update_self ..

def picture (R : Cells.Cut n) (C : Lat.Cut n F) (x : Insertion n F) := (mount R C).roll (reflect R ((mount R C).roll x))

end YM.QCD.RP
