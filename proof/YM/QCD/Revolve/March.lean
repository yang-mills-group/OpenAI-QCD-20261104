import YM.QCD.Revolve.Jolt

/-! # orbit relations at seam 0. Use choices only on later average. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Revolve
open Lat Lattice Wilson Kit Function Finset Quarry
open scoped Matrix Matrix.Norms.L2Operator Topology ContDiff
variable {n:Side}{s t : Signed} {T R : Spike}

def motile {t:Signed}(d e : Site n→ℂ) : Site n → ℂ := fun x=> e x * d (affine t 0 x) -- remove unused
variable {d e : Site n→ℂ}
lemma rocked (h:Glare s 0 0 0 d)(he: Glare t 0 0 0 e): Glare (s*t) 0 0 0 (motile (t:=t) d e):=by
  refine ⟨fun i=>?_,fun i x=>?_⟩
  · obtain ha|ha:=h.sign (affine t 0 i); all_goals unfold motile; rw [ha]; rcases he.sign i with hb|hb <;> rw [hb] <;> simp
  let a:= posDir i
  have hp : affine t (0:Site n) (x+step i)=affine t 0 x+(a.rotate t).vec:=affine_add t 0 x a
  unfold motile; rw [← mul_assoc,he.reflects,hp,mul_assoc,glared h]; simp [affine, Signed.act_mul,Step.rotate_mul,mul_assoc]
lemma troops (d e: Site n→ℂ)(P Q:Spike)(s t : Signed): hues 0 (s*t) (motile (t:=t) d e) (P*Q)=hues 0 t e Q*hues 0 s d P:=by
  unfold hues; rw [ride_mul]; congr 1
  · ext1 x; simp [shiftE]; exact Signed.act_mul _ _ _
  funext i; unfold motile; rw [star_mul, ← wave_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]; rfl
lemma parallel_ink (h:Glare s (0:Site n) 0 0 d)(he:Glare s 0 0 0 e):∃ c:ℂ,c*c=1 ∧ star c=c∧ ∀ i,e i=c*d i:=by
  have hA x i: d x * shimmer (0:Site n) (affine s 0 x) (List.map (·.rotate s) i) = shimmer (0:Site n) x i * d (stop x i):=(flare_path h i x).symm
  refine ⟨e 0*d 0,?_,?_,fun i=> ?_⟩
  · rcases h.sign 0 with h|h <;> rcases he.sign 0 with he|he <;> rw [h,he] <;> simp
  · rcases h.sign 0 with h|h <;> rcases he.sign 0 with he|he <;> rw [h,he] <;> simp
  let w:= route 0 (lift i) 1
  have H:=flare_path he w 0; have hT:= hA 0 w; rw [show stop (0:Site n) w=i from by rw [wrap_stop,show stop _ _ = _ from route_end 0 (lift i) 1,wrap_lift,zero_add]] at H hT -- inspect
  let A:= shimmer 0 (0:Site n) w
  have hN : A≠0:=by unfold A; rw [Quarry.occ_rays]; exact norm_ne_zero_iff.mp (by rw [Flume.pathLength]; norm_num)
  apply mul_left_cancel₀ hN
  change shimmer _ _ _*_= _; rw [H]; rcases h.sign 0 with he|he <;> simp only [he, one_mul,mul_one, neg_mul,mul_neg] at *
  · rw [hT]; unfold A; ring
  rw [← neg_inj,← mul_neg, hT]; unfold A; ring
lemma ambiguous (h:Glare s 0 0 0 d)(hk:Swing s T)(he:Glare s 0 0 0 e)(hp:Swing s R) (F:Sheet n): aura (star (hues 0 s d T)) F = aura (star (hues 0 s e R)) F:= by
  obtain ⟨c,hc,h0,C⟩:= parallel_ink he h
  obtain ⟨p,hp,H⟩:=squad hk hp
  let B:=hues 0 s e R
  have he : hues 0 s d T=(c*star p) • B:=by
    unfold B hues; rw [H,star_smul,show wave (star p • star R)=star p • wave (star R) from (Matrix.smul_kronecker ..),ride_smul]
    congr 1; funext i; rw [C]; simp only [Pi.smul_apply,smul_smul]; rw [mul_right_comm]
  rw [he,star_smul, aura,aura]; simp only [star_smul,star_star,Matrix.smul_mul,Matrix.mul_smul,smul_smul]; rw [show (c*star p)*star (c*star p)=1 from ?_,one_smul]; change _= _; try rfl
  rw [star_mul,h0, star_star]; grind

def starTraffic (s: Signed) := (Swing.goes s).choose
lemma fleetLeft (s:Signed): Swing s (starTraffic s):= (Swing.goes s).choose_spec
def gem (s: Signed)(n:Side):= (shades s (0:Site n) 0 0).choose
lemma gems (s: Signed)(n:Side):Glare s (0:Site n) 0 0 (gem s n):= (shades ..).choose_spec

def scaleA (s: Signed) (n:Side):= hues 0 s (gem s n) (starTraffic s)
lemma compass_eq (h: Glare s 0 0 0 d) (hp:Swing s R)(F:Sheet n):aura (star (hues 0 s d R)) F= aura (star (scaleA s n)) F:= ambiguous h hp (gems ..) (fleetLeft ..) _
end YM.QCD.Revolve
