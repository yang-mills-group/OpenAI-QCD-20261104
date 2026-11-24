import YM.Gust.Whirl
import YM.Gust.Empt
set_option autoImplicit false
set_option maxHeartbeats 620000
noncomputable section
namespace YM.Massive.Gust
open Function Set Filter Analysis MeasureTheory Tarn Tarn.Choir Tarn.Choir.Strip UV Mater Kind Gala
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius ComplexOrder Matrix InnerProductSpace Classical
variable {K: Choir}{C: Sequence}{P:Calibration C}{T:Pollens P K}(hK:K.Domestic)(hf: Foil P K T){m n k:ℕ}
open Tarn.ChargeQ
variable (A:Axis×Axis→K.W) (hA:Persona T A)
local notation "L"=>fun a b=>A (a,b)
variable (J:Axle K (fun a b=>A (a,b))) (U:Vane J)
variable (x:Points (m+1))(hx:x∈conf _)(p:Fin (m+1)→K.W) (g:Ortho.Skew)(s:Fin (m+1)→Bool)(hp:∀ i,p i∈Col T (s i))(i:Fin (m+1))
open Outer Work.A01
local notation "r_"=> Equiv.swap 0 i
noncomputable abbrev powerΛ (a:Axis)(w:Axis)(c:ℕ) (z:E4):= vane a w w c a z
-- local Φ.Deck.
private lemma zcons (t:Points m)(q:Fin m→K.W)(y:E4)(u:K.W): (y,u)::grove K q t=grove K (Fin.cons u q) (Points.cons y t):=by unfold grove; rw [List.ofFn_succ]; rfl -- maybe rfl yep.
include hK hA hf hx
lemma oracleK:∃ c:ℂ,c≠0 ∧∀ v:Fin (m+1)→K.W, (∀ i,v i∈Col T (s i)) → K.total (m+1) (stone x i) (v∘ r_)=c*K.total (m+1) x v ∧∀ a b y,Points.cons y x∈conf _→ phot (L) (v ∘ r_) (stone x i) a b y=c* phot (L) v x a b y:=by
       let I:= Fin (m+1); let t:Equiv.Perm I:= r_; let r:= List.ofFn (fun i:I=>i); let u:= List.ofFn (⇑t); have h:u.Perm r:= t.ofFn_comp_perm id
       obtain ⟨c,hc,hH⟩:= orderPres hK hf A hA _ _ s h.symm []; refine ⟨c,hc,fun v he=>?_⟩
       have hα: TwistPlace x.ofLp v ([]++r)= grove K v x:=by unfold TwistPlace r grove; rw[List.nil_append,List.map_ofFn]; rfl
       have hβ: TwistPlace x.ofLp v ([]++u)= grove K (v ∘ t) (stone x i):=by unfold TwistPlace u grove; rw[List.nil_append,List.map_ofFn]; rfl
       have hw:= hH x.ofLp _ he []; constructor
       · rw[hα,List.nil_append,hβ,List.nil_append,grooved,grooved] at hw; exact hw ((garden ..).2 hx)
       intro a b y h; have hz:= hH x.ofLp _ he [(y,A (a,b))]; rw[hα,List.singleton_append,zcons,hβ,List.singleton_append,zcons,grooved,grooved] at hz; exact hz ((garden ..).2 h)
-- contour test separation
abbrev germ (J:Axis→Axis→ K.W)(K':Ortho.Skew)(x:Points (m+1))(q:Fin (m+1)→ K.W)(χ:E4→ℝ)(a b:Axis) : E4→ℂ:=termG J χ (roll K') x q a b
variable (χ:E4→ℝ)(hw:Table.Window (Outer.stone x i) χ)
include hw
omit hw hA hx hf in
private lemma arcZ (G : Ortho.Skew) (J:Axis→Axis→ K.W)  (q : Fin m→K.W) (x : Points (m+1)) (χ)
    (hx : x∈conf _) (w : Table.Window x χ) (B : K.W) :
    fluxG J χ (roll G) x (Fin.cons B q) = Gust.spin J χ G x q B + ∑ b : Axis, (roll G (x 0) b) • gradG J χ b x q B := by
  let u (b : Axis) := roll G (x 0) b
  let T (b : Axis) (a : Axis) y := Complex.ofReal (Analysis.D (basis a) χ y) * phot J (Fin.cons B q) x a b y
  have he (b a : Axis) : Integrable (T b a) := by
    unfold T phot; simpa only [mul_one] using heartShell hx w hK (Fin.cons (J a b) (Fin.cons B q)) a (fun _=> 1) continuous_const
  let F a b := termG J χ (orbital G (x 0)) x (Fin.cons B q) a b
  have hh (a b : Axis) (y : E4) : termG J χ (roll G) x (Fin.cons B q) a b y= F a b y + u b • T b a y := by
    unfold F T termG phot orbital
    have hp : roll G y b = M4.move G.val (y-x 0) b + u b := congr_fun (f:=fun j => roll G y j) (g:=fun j => M4.move G.val (y-x 0) j + roll G (x 0) j) (by
      have hz : roll G y=M4.move G.val (y-x 0) + roll G (x 0) := by unfold roll M4.move; rw [← map_add,sub_add_cancel]
      exact congr_arg WithLp.ofLp hz) b
    rw [hp]; simp [Complex.real_smul]; ring
  unfold fluxG
  have hi a b : integral volume (termG J χ (roll G) x (Fin.cons B q) a b)=(∫ y,F a b y) + u b • ∫ y,T b a y := by
    rw [funext (hh a b), integral_add (termG_integrable _ _ _ _ _ hK hx w _ _ (smooth_orbital _ _ _ |>.continuous)) (show Integrable (fun y => u b • T b a y) from (he b a).smul (u b)), integral_smul]
  simp_rw [hi, Finset.sum_add_distrib, neg_add]
  congr 1; rw [Finset.sum_comm]; simp_rw [← Finset.sum_neg_distrib ]
  simp only [gradG,smul_neg,Finset.smul_sum,← Finset.sum_neg_distrib]; rfl

omit hK hA hw hx hf in
private lemma awayW(x:Points (m+1))(χ:E4→ℝ)(j:Fin (m+1))(a:Axis)(hp:x∈conf _)(hw:Table.Window (Outer.stone x j) χ)(y:E4)(hy:D (basis a) χ y≠0):Points.cons y x∈conf _:=by
       have h:= separated_of_D (Points.rearrange_in _ hp) hw hy; apply conf_cons hp; intro i he
       let P:=stone x j; let p:=(Equiv.swap 0 j).symm i; have hp': P p=x i:=by simp[P,p,stone]
       have hc:(Points.cons y P) 0=(Points.cons y P) p.succ:=by simp [Points.cons,hp',he]
       exact p.succ_ne_zero ((show Injective (Points.cons y P).ofLp from h) hc).symm
include hp
lemma arc_cost : (∀ a b, Integrable (fun y:E4=>termG (L) χ (roll g) x p a b y))∧ - (∑ a:Axis,∑ b:Axis, ∫ y:E4, termG (L) χ (roll g) x p a b y) = K.total _ x (update p i (swirl K A J U g (x i) (p i))) :=by
       obtain ⟨c,hc,h⟩:= oracleK hK hf A hA x hx s i
       let r := Equiv.swap 0 i; let u := p ∘ r; let t:= Fin.tail u; let X:= stone x i; have he:=Points.rearrange_in r hx; have hv: Fin.cons (p i) t = p ∘ r :=by rw [←show u 0=p i from (by simp[u,r]),Fin.cons_self_tail]
       have hL(a b :Axis)(y:E4): termG (L) χ (roll g) x p a b y=c⁻¹*termG (L) χ (roll g) X (Fin.cons (p i) t) a b y:=by
             by_cases hz:D (basis a) χ y=0; · simp[termG,hz]
             have hF:= (h p hp).2 a b y (awayW x χ i a hx hw y hz); unfold termG; rw [hv, show K.total _ (Points.cons y X) _=_ from hF]; unfold phot; rw [mul_left_comm c⁻¹,inv_mul_cancel_left₀ hc]
       have hwo(a b:Axis): Integrable (fun y:E4=>termG (L) χ (roll g) x p a b y):=by simp_rw [hL]; exact (termG_integrable _ _ _ _ _ hK he hw a b ((roll_smooth g b).continuous)).const_mul _
       -- cancel at slot
       constructor; · exact hwo
       let v:= p i; let y:= swirl K A J U g (x i) v; have hz:y∈Col T (s i):= coat hK hf A hA J U v g _ (hp i) _
       have hu: update p i y ∘ r= Fin.cons y t:=by
            funext j; induction j using Fin.cases with
            | zero=> simp[r]
            | succ j=> have hh: r j.succ≠i:=by rw [←show r 0=i from Equiv.swap_apply_left ..]; exact r.injective.ne j.succ_ne_zero
                       simp[hh]; rfl
       have hf:= (h (update p i y) (fun j=>by
             by_cases hh:j=i; · subst j; rwa[update_self]
             rw [update_of_ne hh]; exact hp _)).1; change K.total _ X _= _ at hf; rw[hu] at hf
       simp_rw [hL, integral_const_mul,← Finset.mul_sum]; rw [← mul_neg]; change c⁻¹*fluxG (L) χ (roll g) X (Fin.cons v t) =K.total _ x (update p i y); refine Eq.trans (?_ : _=c⁻¹*(K.total (m+1) X (Fin.cons y t))) (by rw [hf,inv_mul_cancel_left₀ hc]); apply congr_arg; have wt:=arcZ hK g (L) t X χ he hw v
       rw [wt]; rw [← heads]; unfold Gust.spin; rw [J.relation g v _ _ χ he hw]; simp_rw [U.snaps _ X t χ he hw]; unfold y swirl; rw [map_add,map_sum]; congr 1; apply Finset.sum_congr rfl; intro b _; rw [map_smul,Complex.real_smul,smul_eq_mul]; rw [show X 0=x i from (by simp[X,stone])]
end YM.Massive.Gust
#print axioms YM.Massive.Gust.arc_cost
