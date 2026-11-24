import YM.Gall.Mulct
/-! Translating Cartan probes. Comparison uniform at pose metric. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria.Gall
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.L2Operator TensorProduct Classical InnerProductSpace Interval
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead Oriole Poised Poised.Beacon
variable {u t a D C v e s:ℝ}{c:Side}{n j d m r k p w:ℕ}{F:∀ c:Side, Cray c}
local notation "Y★"=> Cray c
noncomputable def skip0 (Y:∀ c:Side, Cray c):∀ c:Side,Cray c:= fun c=> (c.val:ℝ) • Y c
lemma darts (h:Dart p F)(hh:∀ (c:Side)(i:Edge (Site c)),frost0 i.1→ F c i=0): Dart (p+1) (skip0 F):=by
    obtain ⟨f,hf,hF⟩:=h; refine ⟨f*24,mul_nonneg hf (by norm_num),fun c i=>?_⟩
    unfold skip0; rw [Pi.smul_apply,norm_smul]; by_cases hr:frost0 i.1; · rw [hh c i hr,norm_zero,mul_zero]; exact mul_nonneg (mul_nonneg hf (by norm_num)) (pin_peg ..).le
    rw [Real.norm_of_nonneg (by positivity)]; have hp:(c.val:ℝ)≤ 24*(1+pdist i.1:ℝ):=by
       unfold frost0 at hr; have he: (c.val:ℝ)≤ 8*((pdist i.1:ℝ)+3):=by exact_mod_cast Nat.le_of_not_gt hr
       linarith [Nat.cast_nonneg (α:=ℝ) (pdist i.1)]
    exact (mul_le_mul hp (hF c i) (norm_nonneg _) (by positivity)).trans_eq (by unfold peg; rw [pow_succ]; ring)
def ballU (k:Axis)(p:Cover)(s:ℝ): Prop:= p=step k∧ s=1∨ p = -(step k)∧ s= -1
variable (T:Taper)(g:su.Color)(k:Axis)(p:Cover)
local notation "s₀"=>s
variable (hK: ballU k p s)
include hK
lemma nearbyB: Nearby p:=by rcases hK with h|h; exact ⟨_,Or.inl h.1⟩; exact ⟨_,Or.inr h.1⟩ -- needs include
lemma sailGo (i: Edge (Site c))(h:frost0 i.1)(u:ℝ)(hu:u∈ Set.Icc 0 1): sailT T i u=1 ∧ sailT T (i.1+wrap c p,i.2) u=1 ∧ wake (i.1+wrap c p,i.2) u = wake i u+s • basis k:= by
    have hx:pdist (i.1+wrap c p)≤ pdist i.1+1:=by apply le_trans (pdist_triangle ..); refine Nat.add_le_add_left ((flipT p k ?_).1) _; exact hK.imp And.left And.left
    have hz: frost0 i.1:=h; unfold frost0 at h; refine ⟨ivoryT T i u hu (by omega), ivoryT T (i.1+_,i.2) u hu (by simp only[]; omega),?_⟩
    change lit (i.1+_) + u • _ = lit i.1 + u • basis i.2 + s • basis k; rcases hK with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · rw[wrap_step,lift_c T _ _ hz,one_smul]; abel
    rw [map_neg,wrap_step,←sub_eq_add_neg, lift_d T _ _ hz,neg_one_smul]; abel
omit hK
variable (s)
noncomputable def whip (X:Labels.Taylor su 0)(c:Side) : Cray c :=glaze (fun i:Site c=> curveT (0:E4→L[ℝ]E4→L[ℝ]ℝ) (alo (fun i=> axisC g X i (s • basis k))) (lit i))
noncomputable def whirr (Y: Labels.Taylor su 1) (c:Side): Cray c:= glaze (fun i:Site c=> curveT (s • adept (gone g Y k)) (alo (fun i=> axisC g Y i (s • basis k))) (lit i))
variable {s}
-- explicit pack gradients. U comments
noncomputable def loot (X:Labels.Taylor su 0)(s:ℝ)(c:Side): Cray c:= floats p (fling g T X)-(fling g T X+whip (s:=s) g k X c)
noncomputable def wax (Y: Labels.Taylor su 1)(s:ℝ)(c: Side):Cray c:=floats p (fling g T Y)-(fling g T Y+s • (fling g T (radial Y k))+whirr (s:=s) g k Y c)
include hK
lemma whap (X:Labels.Taylor su 0)(i: Edge (Site c))(h:frost0 i.1): loot T g k p X s c i=0:=by
    let m:=alo (fun j=> axisC g X j (s • basis k)); let e:= (i.1+wrap c p,i.2); let M(x:E4):= curveT 0 m x
    apply sub_eq_zero.mpr; change fling g T X e= fling g T X i+ glaze (fun i'=> M (lit i')) i; unfold M; rw[towing T _ _ (by intros; rfl) i h]; unfold fling; rw [←intervalIntegral.integral_add ((tinge_c ..).intervalIntegrable ..)]; refine intervalIntegral.integral_congr fun x hx=>?_ ; obtain ⟨h1,h2,h3⟩:=sailGo T k p hK i h x (by simpa using hx); unfold tinge; change sailT T e x* axisC g X i.2 (wake e x)= _; rw [h1,show sailT T e x=1 from h2,one_mul,one_mul,show wake e x= _ from h3,minusWave, show m (basis i.2)= _ from aloB ..]; simp
    apply Continuous.intervalIntegrable; simp; exact continuous_const
lemma wharf (Y:Labels.Taylor su 1)(i:Edge (Site c))(h:frost0 i.1): wax T g k p Y s c i=0:=by
    let m:=alo (fun j=> axisC g Y j (s • basis k)); let V:= adept (gone g Y k); let e:= (i.1+wrap c p,i.2); let M(x:E4):= curveT (s • V) m x
    have he(x y:E4): (s • V) x y=(s • V) y x:=by change s • V x y=s • V y x; rw [show V x y= V y x from adeptS _ (fun i j=>goneR g Y i j k) _ _]
    apply sub_eq_zero.mpr; change fling g T Y e= fling g T Y i+s*fling g T (radial Y k) i+glaze (fun i'=> M (lit i')) i; unfold M; rw [towing T _ _ he i h]; unfold fling; rw [← intervalIntegral.integral_const_mul, ←intervalIntegral.integral_add,← intervalIntegral.integral_add]; refine intervalIntegral.integral_congr fun x hx=>?_ ; obtain ⟨h1,h2,h3⟩:=sailGo T k p hK i h x (by simpa using hx); unfold tinge; change sailT T e x* axisC g Y i.2 (wake e x)= _; rw[h1, show sailT T e x=1 from h2, one_mul,one_mul,one_mul,show wake e x= _ from h3,minusWind, show (s • V) (basis i.2) (wake i x)=s*gone g Y k i.2 (wake i x) from (by change s* V (basis i.2) (wake i x)=_; rw [show V (basis i.2) _= _ from adept_basis ..]), show m (basis i.2)= _ from aloB ..]; ring
    · exact ((tinge_c g T Y i).add (continuous_const.mul (tinge_c g T (radial Y k) i))).intervalIntegrable ..
    · exact ((((s • V) (basis i.2)).continuous.comp (wake_c i)).add continuous_const).intervalIntegrable ..
    · exact (tinge_c ..).intervalIntegrable ..
    exact (continuous_const.mul (tinge_c g T (radial Y k) i)).intervalIntegrable ..
lemma sunLoot (X:Labels.Taylor su 0): Dart 3 (skip0 (loot T g k p X s)):=by
    have hx:=dart_weaker (listen T g X) (show 0+1 ≤ 2 by norm_num)
    refine darts (p:=2) (dart_sub (wagons hx p (nearbyB k p hK)) (dart_plus hx (curveCost ..))) ?_; intro c i hi; exact whap T g k p hK X _ hi
lemma sunWax (Y:Labels.Taylor su 1) : Dart 3 (skip0 (wax T g k p Y s)):=by
    have hx:=listen T g Y; have hv:= dart_smul (dart_weaker (listen T g (radial Y k)) (show 0+1 ≤ 2 by norm_num)) s; exact darts (p:=2) (dart_sub (wagons hx p (nearbyB k p hK)) (dart_plus (dart_plus hx hv) (curveCost ..))) fun i j h=> wharf T g k p hK Y j h
end YM.Massive.Patria.Gall
#print axioms YM.Massive.Patria.Gall.sunWax
#print axioms YM.Massive.Patria.Gall.sunLoot
