import YM.QCD.Garden.Quiver

/-! # inherited monomials; costs use **cover** reanchoring. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Garden
open Lat Kit Lattice Wilson Function Finset Filter Metric Tree RG Precision Bloch Laurent
open Orbit Flume Sparks Quarry Stationary YM.Next.Free Pine Eyrie Revolve Rudder
open Extra Iteration Placement QCD.Run Work.F08 Exterior
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator ContDiff Classical
variable {a b c f L:Side}{j k m:ℕ}
abbrev Note (m:ℕ):= Cover × Cover × Address m

def mer (R:Columns L)(W:Bloom m)(r:Site L)(s:PlaqAxes)(i : Fin m)(y:Cover):= R none (arrives r (W.petals i).offset,plaquette (W.petals i).plaq) (plaquette s) y
def brew (R:Columns L)(W:Bloom m)(r:Site L)(z:Address m):ℝ:=∏ i,mer R W r (z.1 i) i (z.2 i)
variable (P:Flight j k) (R:Columns P.L) (W:Bloom m) (r:Site P.L)
def colourPot (u v:Cover): Bundle→Bundle:= fun X=> unFork P r u *X*fork P (arrives r (stop 0 W.tail)) v
def probeEnd (w:Walk)(r:Site L)(u v : Cover):= Work.F08.carry r (stop 0 w)+v-u
def distend (s:Slot)(r:Site L)(u v:Cover):= Work.F08.carry r s.offset+v-u

def jar (n:Note m) : Bloom m:= let u:=n.1; let v:=n.2.1; let z:=n.2.2
                                    { tail:=radial (probeEnd W.tail r u v),petals:=fun i=>slot (distend (W.petals i) r u (z.2 i)) (z.1 i), coeff:=fun i=> ((brew R W r z:ℝ):ℂ) • colourPot P W r u v (W.coeff i)}
lemma jar_deep (u v z x): (jar P R W r (u,v,z)).hues x=((brew R W r z:ℝ):ℂ) • colourPot P W r u v (W.hues x):=by
  unfold jar Bloom.hues colourPot; dsimp only; rw [Matrix.mul_sum, Matrix.sum_mul,Finset.smul_sum]; refine sum_congr rfl fun i _=>?_ ; rw [Matrix.mul_smul,Matrix.smul_mul,smul_comm]
lemma ch_color (A : Mat)(B:Bundle)(h:B∈Moon): Commute (touch A) B:= by obtain ⟨a,rfl⟩:=h; exact interlace ..
lemma jar_spin (h:W.Spins)(n:Note m): (jar P R W r n).Spins:=by
  rcases n with ⟨u,v,z⟩; intro d x; rw [jar_deep,jar_deep,h,Matrix.mul_smul, Matrix.smul_mul]; congr 1; unfold colourPot; set A:=colour d
  have hv : star (touch A) =touch (star A):=touch_star ..
  rw [hv,← Matrix.mul_assoc,← Matrix.mul_assoc, (ch_color A _ (pillar_l ..)).symm.eq]; simp only [Matrix.mul_assoc]; rw [(ch_color (star A) _ (pillar ..)).eq]

variable {η σ B C :ℝ}
lemma jar_price (u v z):
    (jar P R W r (u,v,z)).price ≤ |brew R W r z| *(‖unFork P r u‖* W.price *‖fork P (arrives r (stop 0 W.tail)) v‖) := by
  unfold Bloom.price; rw [mul_sum,sum_mul,mul_sum]; refine sum_le_sum fun i _=>?_ ; unfold jar colourPot; dsimp only; rw [norm_smul,Complex.norm_real,Real.norm_eq_abs]; apply mul_le_mul_of_nonneg_left _ (abs_nonneg _); exact (norm_mul_le ..).trans (mul_le_mul_of_nonneg_right (norm_mul_le ..) (norm_nonneg _))

lemma dlm (w:Walk)(r:Site L)(u v: Cover)(he:0≤η)(hfit:η≤ σ*L.val):
    η*(size (probeEnd w r u v):ℝ)≤ σ*w.length+η*size u+η*size v+4*η:=by
  have hL:=side_pos L
  let p:= Work.F08.carry r (stop 0 w); have hx:=carry_bound r (stop 0 w); let s: Cover→ℕ:= Laurent.size
  have hr : (s p:ℝ)≤ w.length/(L.val:ℝ)+4:=hx.trans (by gcongr; exact (by simpa [size] using end_size 0 w)) -- mod cast
  have hp : (size (probeEnd w r u v):ℝ)≤ (s p:ℝ)+s u+s v:=by
    have hz : s (p+v-u) ≤ s p+s u+s v:=by
      rw [sub_eq_add_neg]; apply (size_add ..).trans; rw [size_neg]; have ht:= size_add p v; dsimp only [s]; dsimp only [s] at *; omega
    exact_mod_cast hz
  calc
    _ ≤ η*(↑(s p)+(s u:ℝ)+s v):=mul_le_mul_of_nonneg_left hp he
    _ ≤ η*((w.length/(L.val:ℝ)+4)+(s u:ℝ)+s v):=by gcongr
    _ = η/(L.val:ℝ)*w.length+η*s u+η*s v+4*η:=by ring
    _ ≤ _:=by dsimp only [s]; gcongr; exact (div_le_iff₀ hL).2 hfit

lemma tms (u v : Cover)(z:Address m)(he:0≤η)(hfit:η≤σ*P.L.val):
    η*(jar P R W r (u,v,z)).span ≤ σ*W.span + (4+8*(m:ℝ))*η + (η*(1+m))*size u+η*size v+ ∑ i,η*size (z.2 i):=by
  have hp : 0≤ σ:=nonneg_of_mul_nonneg_left (he.trans hfit) (side_pos P.L)
  have hf i: η * (size (distend (W.petals i) r u (z.2 i)) + 4:ℕ) ≤ σ * (W.petals i).length + η * size u + η*size (z.2 i) + 8*η:=by
    push_cast; rw [mul_add]; have hx : η * size (distend (W.petals i) r u (z.2 i))≤ σ*(W.petals i).walk.length+η*size u+η*size (z.2 i)+4*η:=dlm (W.petals i).walk r u (z.2 i) he hfit
    have hz : ((W.petals i).walk.length:ℝ)≤ (W.petals i).length:= by exact_mod_cast Nat.le_add_right (W.petals i).walk.length 4
    nlinarith
  have hh:= sum_le_sum (s:=univ) fun i _=> hf i; simp_rw [sum_add_distrib,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at hh
  unfold jar Bloom.span; dsimp only; simp_rw [rad_length,slot_length, Nat.cast_add,Nat.cast_sum,mul_add,mul_sum]; -- inspect
  have h:= dlm W.tail r u v he hfit; linarith
end YM.QCD.Garden
