import YM.Bloom.Jar
import YM.Arise.Unit
/-! # global crossing estimates on charges, posture invariant family true lifts. -/
set_option autoImplicit false
noncomputable section
namespace YM.Bloom
open Function Lattice Laurent Bloch Metric RG Filter
open Finset YM.Bank Precision Matrix Exterior Arise Arise.Range Jar
open YM.Bank.Jule 
open Ivo Pic Maxwell
open AnalyticBridge.LocalGaussianLaws.Current
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator ContDiff
variable {k p r m j n:ℕ}{a t M e b:ℝ}{c f:Side}
variable (l u:List Axis)
lemma sun (G: E4→ℂ)(h:∀ x,x≠0→ ContDiffAt ℝ ∞ G x) (x:E4)(hx:x≠0): ContinuousAt (stove G l u) x:=by
     change ContinuousAt ((-1:ℂ)^u.length • deriveL u (deriveL l G)) x; exact (continuousAt_const.smul (balla u (deriveL l G) away open_away (balla l G away open_away h) x hx).continuousAt)
section Gauge
structure Grain (a t M:ℝ)(F: Bed)(c:Side): Prop where
    strip : F.metric.strip t M
    noteN : Numeric (F.metric.acts c) a M
    metric : F.metric.read 0=1
variable (i v: PlaqAxes)
def know (i v:PlaqAxes)(c:Side)(F:Bed)(x y:Cover)(X Y:Parc):ℂ:= pairP c (learned F c) x y (plaquette i) (plaquette v) X Y
lemma stampF(x y z w: Cover)(F:Bed)(c: Side) : know i v c F x y (strike l z) (strike u w)= glyph F i v l u (x+z) (y+w) c:=by
      have he:=couple x y (plaquette i) l (learned F c) (1: Matrix (Co c (TypeFace 2)) (Co c (TypeFace 2)) ℝ) (plaquette v) z w u; rw [Matrix.mul_one,Matrix.mul_one] at he; exact congr_arg ((↑):ℝ→ℂ) he
lemma sage (hn:8+p+r≤n)(ha:0<a)(ht:0<t)(hm:0≤M): Vows (know i v) (Grain a t M) (stove (from_p i v)) n 4 p r:=by
     intro w u hp hr x y b e he; obtain ⟨C,hc,H⟩:= calf (by positivity:0< e/2) (b+1) a t M ha ht hm i v w u (by omega : 1+w.length+u.length+7≤n); refine ⟨C,hc,eaves _|>.2 ?_⟩
     filter_upwards [H,shelves (n:=n) (by omega) he b (x-y)] with W hw hh z hz; filter_upwards [hw _ (hh z hz)] with c hc x' y' A ha hv'; rw [stampF]; exact hc A hv'.strip hv'.noteN hv'.metric _ _ (by rw [← ha]; abel)
lemma stipend(l u:List Axis)(x:E4)(hx:x≠0): ContinuousAt (stove (from_p i v) l u) x:= by
    apply sun _ _ _ (fun z hz=>?_ ) x hx; exact Complex.ofRealCLM.contDiff.contDiffAt.comp z (Bare.curl_diff hz i.val.1 i.val.2 v.val.1 v.val.2)
lemma gauges (hn:10+p+r ≤ n)(ha:0<a)(ht:0<t)(hm:0≤M)(he:0<e)(b:ℝ)(hp:l.length ≤ p)(hr:u.length ≤ r)(X Y:Parc)(hx: Rocky (some i) l p X)(hy: Rocky (some v) u r Y): ∃ C:ℝ,0≤ C∧∀ᶠ w:ℝ in atTop,∀ z:Cover,posT w n z∈ Oasis e b→∀ᶠ f: Side in atTop,∀ x y:Cover,∀ A:Bed, x-y=z → Grain a t M A f →
      w*‖(w^n)^(4+l.length+u.length) • know i v f A x y X Y - stove (from_p i v) l u (posT w n z)‖ ≤ C:=by
    let V:=Complex.ofRealCLM.toLinearMap; let L:=fun f (A:Bed) x y P=> V ∘ₗ wishedL f (learned A f) x y (plaquette i) (plaquette v) P; let R:=fun f (A:Bed) x y P=>V ∘ₗ wishedR f (learned A f) x y (plaquette i) (plaquette v) P
    obtain ⟨C,hc,H⟩:= shelfFunds (know i v) L R l u (fun _ _ _ _ _ _=>rfl) (fun _ _ _ _ _ _=> rfl) (sage i v (p:=p+1) (r:=r+1) (n:=n) (by omega) ha ht hm) (by omega) he b (fun l s x _ _ H=>stipend _ _ _ _ x H) hp hr X Y _ _ hx hy; refine ⟨C,hc,eaves _|>.1 H⟩ -- eaves P default
end Gauge
section Spin
open QCD QCD.Lat QCD.Bloom QCD.Bank Next.Free QCD.Free QCD.Flume
variable (g h:Fiber)
def heal (f:Side)(D:Train j)(x y:Cover) (a b:Parc) :ℂ := pairS f (stage D f) x y g h a b
lemma honor(x y z w: Cover)(D:Train j)(c: Side) : heal g h c D x y (strike l z) (strike u w) = Sway D c g h (x+z) (y+w) l u:=by
    have he:=sells x y l (1:Sheet c) 1 (stage D c) g h z w u; rw [Matrix.mul_one,Matrix.mul_one] at he; exact he
lemma scores (hn:7+p+r≤n)(hj:2 ≤ j): Vows (heal g h) (fun (_:Train j) _=>True) (stove (s_k g h)) n 3 p r:=by
    intro w u hp hr x y b e he; obtain ⟨C,hc,H⟩:= pence (by positivity:0<e/2) (b+1) j hj g h w u (by omega : w.length+u.length+7 ≤ n); refine ⟨C,hc,eaves _|>.2 ?_⟩
    filter_upwards [H,shelves (n:=n) (by omega) he b (x-y)] with W hw hh z hz; filter_upwards [hw _ (hh z hz)] with c hc x' y' A ha _; rw [honor]; exact hc _ _ _ (by rw [← ha]; abel)
lemma swipe_p (l u:List Axis)(x:E4)(hx:x≠0): ContinuousAt (stove (s_k g h) l u) x:=by
     apply sun _ _ _ (fun z hz=>?_ ) x hx; by_cases hp:g.2=h.2
     · rw [show s_k g h= Massive.UV.Free.dirac g.1 h.1 from funext fun _=> if_pos hp]; exact Arise.Range.is_hot _ _ _ hz
     rw [show s_k g h=(fun _=>0) from funext fun _=>if_neg hp]; exact contDiffAt_const
lemma spin_cost (hn:9+p+r ≤ n)(hj: 2 ≤ j)(he:0<e)(b:ℝ)(hp:l.length ≤ p)(hr:u.length ≤ r)(X Y:Parc)(hx:Rocky none l p X)(hy:Rocky none u r Y): ∃ C:ℝ,0≤ C ∧∀ᶠ w:ℝ in atTop,∀ z:Cover,posT w n z∈ Oasis e b→∀ᶠ f:Side in atTop,∀ x y:Cover,∀ D:Train j,x-y=z →
      w*‖(w^n)^(3+l.length+u.length) • heal g h f D x y X Y - stove (s_k g h) l u (posT w n z)‖ ≤ C:=by
     obtain ⟨C,hc,H⟩:= shelfFunds (heal g h) (fun f D x y X=>waryL f (stage D f) x y g h X) (fun f D x y X=>waryR f (stage D f) x y g h X) l u (fun _ _ _ _ _ _=>rfl) (fun _ _ _ _ _ _=>rfl) (scores g h (p:=p+1) (r:=r+1) (n:=n) (by omega) hj) (by omega) he b (fun l s x _ _ H=>swipe_p _ _ _ _ x H) hp hr X Y _ _ hx hy; rw [eaves] at H; exact ⟨C,hc,by simpa using H⟩
end Spin
end YM.Bloom
#print axioms YM.Bloom.spin_cost
#print axioms YM.Bloom.gauges
