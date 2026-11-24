import YM.QCD.Revolve.Wrap
import YM.QCD.Cedar.Canopy

/-! # rotation covariance of the all-field reference kernels -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Revolve
open Lat Lattice Function Finset Wilson Kit
open Pine Flume
open RG Laurent Bloch YM.Next.Free
open scoped Matrix Matrix.Norms.L2Operator BigOperators
variable {n : Side} {s : Signed} {b t t' : Site n} {l : Site n→ℂ} {P : Spike} {j k : ℕ} (h : Glare s t t' b l) (hp : Swing s P)

def aura (T : Sheet n) (X : Sheet n):= T*X*star T
lemma aura_one {T : Sheet n} (hT : T∈unitary _) : aura T 1=1:=by rw [aura,mul_one]; exact hT.2
lemma aura_scale (T X : Sheet n) (A : ℂ) : aura T (A • X)=A • aura T X:=by rw [aura, Matrix.mul_smul,Matrix.smul_mul]; rfl
lemma aura_add (T X Y : Sheet n): aura T (X+Y)=aura T X+aura T Y:=by rw [aura,mul_add,add_mul]; rfl
lemma aura_sub (T X Y : Sheet n): aura T (X-Y)=aura T X-aura T Y:=by rw [aura,mul_sub,sub_mul]; rfl
lemma aura_ad (T X : Sheet n):aura T (star X)=star (aura T X):= by simp [aura,mul_assoc]
lemma aura_neg (T X : Sheet n):aura T (-X)=-(aura T X):=by simp [aura]
lemma aura_prod {T : Sheet n} (h : T∈unitary _) (X Y: Sheet n): aura T (X*Y)=aura T X*aura T Y:=by simp only [aura,mul_assoc]; rw [← mul_assoc (star T) T,h.1,one_mul]
include h hp
lemma route_shift (x : Cover) (U : Grid n) (o : Lattice.Order) : routeM t (pull s b U) (route 0 x o) =
    aura (hues b s l P) (routeM t' U (route 0 (s.act x) (orderEquiv s o))):=by rw [hue_path h hp, send_route _ _ _ _ 0]; simp [aura,affine]
lemma spin_mote (x : Cover) (U : Grid n) : mote t (pull s b U) x=aura (hues b s l P) (mote t' U (s.act x)):=by
  unfold mote; rw [aura_scale]; congr 1; unfold aura; rw [Finset.mul_sum,sum_mul, ← Equiv.sum_comp (orderEquiv s) (fun i=>hues b s l P*routeM t' U (route 0 (s.act x) i)*star _)]; -- likely wrong occurrences
  exact Finset.sum_congr rfl fun i _=> route_shift h hp x U _
lemma spin_deck {p : Cover→ℝ} (hs : Summable fun i=>‖p i‖) (U : Grid n) :
    deck t (pull s b U) (p∘s.act)=aura (hues b s l P) (deck t' U p):=by
  let T:= hues b s l P
  unfold deck aura; rw [← Summable.tsum_mul_left _ ((motes hs ..).of_norm), ← Summable.tsum_mul_right, ← (Signed.actEquiv (R:=ℤ) s).toEquiv.tsum_eq (fun i=> T*((p i:ℂ) • mote t' U i)*star T)]
  · refine tsum_congr fun i=>?_
    change (p (s.act i):ℂ) • _=aura T _; rw [spin_mote h hp,aura_scale]; rfl
  exact (motes hs ..).of_norm.mul_left _
lemma spin_wall (v : Train j) (K : Plan j) (U : Grid n) (a : Axis) : walls K t v (pull s b U) a=aura (hues b s l P) (walls K t' v U (s.perm a)):=by
  let T := hues b s l P; let F:= deck t' U (K.Herm v (s.perm a)); let x:= arcL t' U (s.perm a)
  have ht : deck t (pull s b U) (K.Herm v a)=aura T F := by
    rw [← show K.Herm v (s.perm a)∘s.act=K.Herm v a from funext (K.herm_sym v a s)]
    exact spin_deck h hp (Herm_valid ..) U
  have hT : T∈unitary _ := colour_wheel h hp
  have hz : arcL t (pull s b U) a = if s.flip a then aura T (star x) else aura T x:=by
    rw [arcL,hue_march h hp]; cases he : s.flip a
    · simp only [he,Bool.false_eq_true,↓reduceIte]; unfold x arcL; rw [aura_sub,aura_one hT]; rfl
    simp only [he,if_true]; unfold x arcL; rw [star_sub,star_one,aura_sub,aura_one hT]; rfl
  unfold walls; rw [ht, hz]; dsimp only; change _=aura T ((K.μ:ℂ) • leaves x+ half (leaves (F*x)) (leaves (F*star x)))
  have hy (X : Sheet n) : aura T (leaves X)=leaves (aura T X):=by rw [leaves,aura_prod hT,aura_ad]; rfl
  split_ifs
  · rw [aura_add,aura_scale,half,half,aura_scale,aura_add,hy,hy,hy,aura_prod hT F x,aura_prod hT F (star x),aura_ad T x,star_star,← aura_ad T x,add_comm (leaves (aura T F *_)), ← hy (star x)] -- fix
    rw [show leaves (star x)=leaves x from lawful ..,hy]
  rw [aura_add,aura_scale,half,half,aura_scale,aura_add,hy,hy,hy,aura_prod hT,aura_prod hT,aura_ad T x]
lemma spin_veins (v : Train j) (hj : 2≤j) (U : Grid n) (a : Axis) : vein t v a (pull s b U) = aura (hues b s l P) (vein t' v (s.perm a) U):=by
  unfold vein; rw [hue_gamma h hp,aura_prod (colour_wheel h hp)]; split_ifs with hi
  · have hh : Flume.alphaT v (s.perm a) ∘ s.act= fun i=> -alphaT v a i:= funext fun i=> (negative_al hj s v a i).trans (if_pos hi)
    have he:= spin_deck h hp (al_snap v (s.perm a) hj) U; rw [hh] at he; dsimp only [deck] at he; simp only [Complex.ofReal_neg,neg_smul, tsum_neg] at he
    change aura _ (-onSpin n _)*_= _; rw [aura_neg]; rw [show aura _ (deck _ _ _) = _ from he.symm]; rw [neg_mul,mul_neg]; rfl
  change aura _ (onSpin n _)*_= _; rw [← spin_deck h hp (al_snap v (s.perm a) hj),show Flume.alphaT v (s.perm a) ∘ s.act= alphaT v a from funext fun i=> (negative_al hj s v a i).trans (if_neg hi)]
lemma spin_wood (v : Train j) (K : Plan j) (U : Grid n) : wood K t v (pull s b U)=aura (hues b s l P) (wood K t' v U):=by
  unfold aura wood; rw [mul_sum,sum_mul,← Equiv.sum_comp s.perm (fun a=>hues b s l P*(walls K t' v U a+skewL (vein t' v a U))*star _)]
  refine sum_congr rfl fun i _=> ?_
  rw [spin_wall h hp,spin_veins h hp v K.good]; change _=aura _ _; rw [aura_add,skewL,skewL,aura_scale,aura_sub,aura_ad]
end YM.QCD.Revolve
