import YM.Vern.Fist
import YM.Vern.City
set_option maxHeartbeats 700000
set_option autoImplicit false
noncomputable section
namespace YM.NativeV
open Function Set Filter Analysis
open scoped Topology BigOperators Classical
open Lobo Vern Finset
variable {W X:Type}[AddCommGroup W][Module ℂ W][AddCommGroup X][Module ℂ X]
-- point space W is higher.Y.X lower
structure Medal (W:Type)[AddCommGroup W][Module ℂ W] where
    T: Tide W
    J:Tri→Module.End ℂ W
    K:Tri→Module.End ℂ W
    unit : ∀ i x y,T.knot (K i x) (K i y)=T.knot x y
    skew : ∀ i,T.Leans (J i)
structure Drift (C:Medal W) (X:Type)[AddCommGroup X][Module ℂ X] where
    d: Axis→ X→ₗ[ℂ]W
    J:Tri→Module.End ℂ X
    K:Tri→Module.End ℂ X
    geo:∀ i a x,C.K i (d (lieu a) x)= (τc i a) • d (lieu (roof i a)) (K i x)
    awe:∀ i x,C.K i (d timeAxis x)=d timeAxis (K i x)
    twist:∀ i x,C.J i (d timeAxis x)=d timeAxis (J i x)
    torque:∀ i j:Tri,∀ x,C.J i (d (lieu j) x)- d (lieu j) (J i x)+(C.J j (d (lieu i) x)- d (lieu i) (J j x))=0
structure Olive (C:Medal W)(p f:ℝ) (T:Tri→Tri→W):Prop where
    cash(k i j): C.J k (T i j)=(p:ℂ) • drive k (fun i=>T i j) i+(f:ℂ) • drive k (T i) j
    cov(k i j): C.K k (T i j)=τc k i • (τc k j • T (roof k i) (roof k j))
local notation "κ"=> τc
local notation "w_"=>waveT
variable (C:Medal W)(J:Drift C X)(p f:ℝ)(T:Tri→Tri→W)(ht:Olive C p f T)
-- shortcut operators and sums.S.
lemma coins' (i j k:Tri): star (τc i j)=τc i j∧ star (waveT i j k)=waveT i j k:=⟨Complex.conj_ofReal _, Complex.conj_ofReal _⟩
lemma snips(u v:W): C.T.knot u 0=0 ∧ C.T.knot u (-v)= -(C.T.knot u v):=⟨C.T.zero' u,map_neg (C.T.zz u) v⟩
lemma snack (k:Tri)(x:Tri→W)(v:W)(a:Tri): C.T.knot (drive k x a) v=∑ i,waveT k a i* C.T.knot (x i) v:=by
       rw[← C.T.con v]; change star (C.T.zz _ _) = _; unfold drive; rw[_root_.map_sum,star_sum]; apply sum_congr rfl; intro i _; change star (C.T.knot v _)=_; rw [C.T.sep,star_mul',(coins' k a i).2,C.T.con]
lemma snackV (k:Tri)(x:Tri→X)(P:X→ₗ[ℂ]W)(a:Tri)(v:W) : C.T.knot v (P (drive k x a))=∑ i,waveT k a i * C.T.knot v (P (x i)):=by
       unfold drive; simp only [_root_.map_sum,_root_.map_smul]; change C.T.zz v _=_; rw [_root_.map_sum]; exact sum_congr rfl fun i _=> C.T.sep ..
lemma sun (k:Tri)(x:Tri→W)(a:Tri)(v:W) : C.T.knot v (drive k x a)=∑ i,waveT k a i * C.T.knot v (x i):= snackV C k x (LinearMap.id) a v
variable (Y:Tri→ W)(e:ℝ)(hJ:∀ i j,C.J i (Y j)= (e:ℂ) • drive i Y j)(hK:∀ i j,C.K i (Y j)=κ i j • Y (roof i j))
variable (he:p ≠ f)
include ht hJ hK he
lemma rain : C.T.knot (T 1 2) (Y 0)=0:=by
     let D(i j k):= C.T.knot (T i j) (Y k); have hz(i m q t:Tri): D m q t= τc i m* τc i q* τc i t* D (roof i m) (roof i q) (roof i t):=by
            unfold D; rw [← C.unit i, ht.cov, hK,C.T.seals,C.T.seals,C.T.sep,(coins' i m q).1,(coins' i q q).1]; ring
     have hj:= C.skew 0 (T 1 1) (Y 0); rw[ht.cash,hJ,C.T.other,C.T.seals,C.T.seals,C.T.sep,show star (↑p:ℂ)=(↑p:ℂ) from Complex.conj_ofReal _,show star (↑f:ℂ)=(↑f:ℂ) from Complex.conj_ofReal _] at hj
     have h0: C.T.knot (T 1 2) (Y 0)=-(C.T.knot (T 2 1) (Y 0)):=by
            have h:= hz 0 1 2 0; rw[show roof 0 2=1 from rfl,show roof 0 1=2 from rfl,show roof 0 0=0 from rfl] at h; simpa +decide [τc,charI] using h
     rw [gammaE _ Y,(snips C _ (0:W)).1,mul_zero,neg_zero,show drive 0 (fun i=> T i 1) 1=_ from gammaY (0:Tri) (fun i=>T i 1), show drive 0 (T 1) 1=_ from gammaY (0:Tri) (T 1)] at hj
     change (p:ℂ)*C.T.knot (T 2 1) (Y 0)+(f:ℂ)*C.T.knot (T 1 2) (Y 0)=0 at hj; rw [h0]; rw [h0,mul_neg,← sub_eq_add_neg, ← sub_mul] at hj; rw [(mul_eq_zero.mp hj).resolve_left (sub_ne_zero.mpr (by exact_mod_cast he)),neg_zero]
omit hJ hK
-- differential vector leak.Point of proof
structure Nation (P:Tri→Tri→X)(e:ℂ):Prop where
    wax:∀ i m q,J.K i (P m q)= κ i m • (κ i q • P (roof i m) (roof i q))
    jeep:∀ i m q,J.J i (P m q)= e • (drive i (fun j=>P j q) m+drive i (P m) q)
    sym:∀ m q,P m q=P q m
variable (P:Tri→Tri→X)(s:ℂ)(hP:Nation C J P s)
noncomputable def Zap (i m q u v:Tri):ℂ:= C.T.knot (T m q) (J.d (lieu i) (P u v))
include hP
lemma spock(k i m q u v:Tri): Zap C J T P i m q u v=κ k i*κ k m* κ k q*κ k u * κ k v* Zap C J T P (roof k i) (roof k m) (roof k q) (roof k u) (roof k v):=by
      unfold Zap; rw [← C.unit k, ht.cov,J.geo,hP.wax,map_smul,map_smul,C.T.seals,C.T.seals,C.T.sep,C.T.sep,C.T.sep,(coins' k m m).1,(coins' k q m).1]; ring
lemma skewM(i j m q u v:Tri): tiltT (Zap C J T P) p f s i j m q u v= -(C.T.knot (T m q) (C.J i (J.d (lieu j) (P u v))- J.d (lieu j) (J.J i (P u v)))):=by
      let x:= P u v; let d:= J.d (lieu j); let V:= T m q; have h:C.T.knot V (C.J i (d x))= -C.T.knot (C.J i V) (d x):=by rw[C.skew i,neg_neg]
      unfold tiltT; rw [sub_eq_add_neg,C.T.add,(snips ..).2, show C.T.knot (T m q) (C.J i _)=_ from h]; -- def goals align
      change _= -(-C.T.knot (C.J i (T m q)) _+ -(C.T.knot _ (J.d _ (J.J i (P u v)))))
      rw [ht.cash,hP.jeep,C.T.other,C.T.seals,C.T.seals,map_smul,map_add,C.T.sep,C.T.add]; simp_rw [snack,snackV]; simp only [Complex.star_def,Complex.conj_ofReal,mul_add,Finset.mul_sum,Finset.sum_add_distrib]
      unfold Zap; simp only [mul_comm (w_ _ _ _) (↑p:ℂ),mul_comm (w_ _ _ _) (↑f:ℂ),mul_comm (w_ _ _ _) s,mul_assoc,neg_add,neg_neg]; -- possible sap shifts
      abel
lemma race : let W:= Zap C J T P; W 1 1 2 1 0=0 ∧ W 2 1 2 2 0=0 ∧ W 0 1 2 0 0=0∧ W 0 1 2 1 1+W 0 1 2 2 2=0:=by
      intro W; apply fist _ p f s (fun i m q u v=> by unfold Zap; rw[hP.sym u v]) (spock C J p f T ht he P s hP) _ (by exact_mod_cast he)
      intro i j m q u v; rw[skewM C J p f T ht he _ s hP,skewM C J p f T ht he _ s hP,← neg_add,← C.T.add,J.torque,Tide.zero',neg_zero]
end YM.NativeV
#print axioms YM.NativeV.race
#print axioms YM.NativeV.rain
