import YM.QCD.Flume.Cool

/-!
# covariant Laurent taps, L2 operators. Shortest paths averaged over order.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Pine
open Lat Cost Lattice Wilson Function Finset Flume
open Laurent Bloch YM.Next.Free Metric Kit Free
open scoped Matrix.Norms.L2Operator Topology BigOperators Matrix
variable {n : Side} {j : ℕ}

def mote (t : Site n) (U : Grid n) (x : Cover) : Sheet n:=(votes:ℂ)⁻¹ • ∑ o, routeM t U (route 0 x o)
def deck (t : Site n) (U : Grid n) (a : Cover→ℝ) := ∑' i, (a i:ℂ) • mote t U i
lemma votes_ne : (votes:ℂ) ≠ 0:=by exact_mod_cast (show votes≠ 0 from Fintype.card_pos.ne')
lemma mote_nil (t : Site n) (U : Grid n) : mote t U 0=1:=by unfold mote; simp_rw [route_same,routeM, List.map_nil,List.prod_nil,sum_const, card_univ]; rw [← Nat.cast_smul_eq_nsmul ℂ,smul_smul,inv_mul_cancel₀ votes_ne,one_smul]
lemma mote_norm (t : Site n) (U : Grid n) (x : Cover) : ‖mote t U x‖ ≤ 1:=by
  rw [mote,norm_smul,norm_inv,Complex.norm_natCast]
  have ht:= (norm_sum_le _ _).trans (sum_le_sum (s:=Finset.univ) fun o _=> rotation_price (Kit.circle t U (route 0 x o)))
  exact (mul_le_mul_of_nonneg_left ht (by positivity)).trans (le_of_eq (by rw [sum_const,card_univ,nsmul_eq_mul,mul_one,inv_mul_cancel₀ Kit.poll_pos.ne']))
lemma motes {a : Cover→ℝ} (h : Summable fun i=>‖a i‖) (t : Site n) (U : Grid n): Summable fun i=> ‖(a i:ℂ) • mote t U i‖:= by apply h.of_nonneg_of_le (fun _=>norm_nonneg _); intro i; rw [norm_smul,Complex.norm_real]; exact mul_le_of_le_one_right (norm_nonneg _) (mote_norm ..)
lemma valueD {σ K : ℝ} (a : Cover→ℝ) (h : Width σ K a) (he : 0≤σ) (t : Site n) (U : Grid n): ‖deck t U a‖≤K:=by
  have hu:= (h.unweighted he).2.1; have ht:= motes hu t U
  refine (norm_tsum_le_tsum_norm ht).trans ((ht.tsum_le_tsum ?_ hu).trans (h.unweighted he).2.2)
  intro i; rw [norm_smul,Complex.norm_real]; exact mul_le_of_le_one_right (norm_nonneg _) (mote_norm ..)
lemma mote_G (t : Site n) (U : Grid n) (s : Frame n) (x : Cover) : mote t (gauge s U) x=siteRot s*mote t U x *star (siteRot s):=by unfold mote; simp only [Matrix.smul_mul,Matrix.mul_smul, Finset.mul_sum, Finset.sum_mul,gaugeM]
lemma motive (t : Site n) (U : Grid n) (s : Frame n) (a : Cover → ℝ) (h : Summable fun i=>‖a i‖) : deck t (gauge s U) a=siteRot s * deck t U a * star (siteRot s):=by
  unfold deck; rw [← Summable.tsum_mul_left _ ((motes h ..).of_norm),← Summable.tsum_mul_right]
  · simp only [mote_G,Matrix.smul_mul,Matrix.mul_smul]
  exact (motes h ..).of_norm.mul_left _
lemma sport (t : Site n) (U : Grid n) (o) (x : Spike): mote t U o*onSpin n x=onSpin n x*mote t U o:=by unfold mote; simp_rw [Matrix.smul_mul,Matrix.mul_smul,Finset.sum_mul,Finset.mul_sum,fun l=> (spinM t U x (route 0 o l)).eq]
lemma sailor (t : Site n) (U : Grid n) (a : Cover → ℝ) (h : Summable fun i=>‖a i‖) (x : Spike):deck t U a*onSpin n x=onSpin n x*deck t U a:=by
  unfold deck
  rw [← Summable.tsum_mul_left _ ((motes h ..).of_norm), ← Summable.tsum_mul_right]
  · simp_rw [Matrix.mul_smul,Matrix.smul_mul,sport]
  exact (motes h ..).of_norm

def peeler (n : Side): Sheet n→ₗ[ℂ] Sheet n := { toFun:= peel,map_add':= peel_add,map_smul':=fun x y=> peel_smul .. }
def chamber (n : Side) : Sheet n →L[ℂ] Sheet n:= (peeler n).toContinuousLinearMap
lemma mote_f (n : Side) (x): peel (mote (0:Site n) 1 x)=lined (fun i=> mode (tuning i) x • 1):=by
  unfold mote; rw [peel_smul]
  change (votes:ℂ)⁻¹ • chamber n _=_; rw [map_sum]
  have he (o:Lattice.Order):chamber n (routeM 0 1 (route 0 x o))=lined (fun i=> mode (tuning i) x • 1):=by change peel _=_; rw [unroll 0 _ 0,route_end]
  simp_rw [he,sum_const, card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ votes_ne,one_smul]
lemma deck_f (n : Side) (a : Cover→ ℝ) (h : Summable fun i=>‖a i‖): peel (deck (0:Site n) 1 a)=lined (fun i=> RRead a (tuning i) • 1):=by
  have hp := ((chamber n).hasSum (motes h (0:Site n) 1).of_norm.hasSum)
  have he (x): chamber n ((a x:ℂ) • mote 0 1 x)=(a x:ℂ) • lined (fun i=> mode (tuning i) x • 1) := by rw [map_smul]; change _ • peel _=_; rw [mote_f]
  simp_rw [he] at hp
  ext ⟨i,k⟩ ⟨j,l⟩
  have ht : HasSum (fun x=> ((a x:ℂ) • lined (n:=n) (fun i=> mode (tuning i) x • 1)) (i,k) (j,l)) (chamber n (deck 0 1 a) (i,k) (j,l)):= by
    let L : Sheet n →ₗ[ℂ] ℂ := { toFun:=fun A=> A (i,k) (j,l),map_add':=fun A B=> rfl,map_smul':=fun _ _=> rfl }
    exact L.toContinuousLinearMap.hasSum hp
  change chamber n _ (i,k) (j,l)=_; rw [← ht.tsum_eq]
  simp only [lined, rr, Matrix.smul_apply, Equiv.refl_apply,RRead]; split
  · unfold Laurent.read; simp only [smul_eq_mul]; rw [← tsum_mul_right]; exact tsum_congr fun x=>by ring
  simp
@[fun_prop] lemma persist (a : Cover→ℝ) (t : Site n) (ha : Summable fun i=>‖a i‖): Continuous fun U => deck t U a:=by
  unfold deck; refine continuous_tsum ?_ ha ?_
  · intro i; unfold mote; fun_prop
  intro i U; rw [norm_smul,Complex.norm_real]; exact mul_le_of_le_one_right (norm_nonneg _) (mote_norm ..)
end YM.QCD.Pine
