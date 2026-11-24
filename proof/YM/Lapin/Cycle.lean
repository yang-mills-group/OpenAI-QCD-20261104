import YM.Lapin.Craft
/-! Total Ward price transmitted on both stencil moment waves. Single-volume slope, not yet thermo limit. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Massive.Patria.Gall
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.L2Operator TensorProduct Classical InnerProductSpace
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead Oriole Poised Poised.Beacon Kit Push.Local
open Tawny Tawny.Cast.Rays
variable {D:ℝ}{c:Side}{n l d m r k p q w i N:ℕ}{U:BudgetPoint}
local notation "Y★"=> Cray c
local notation "G★"=> Lat.Fields c 6
open QCD.Revolve TorusPCAC.Geometry Lining Lining.Ferry Lining.Temper Canvas PCAC Patria Patria.Depth Patria.Rolls PCAC.Oren
variable {S:Scheme}{R:Side}(A:Massive.Run S N R 6)(hA:A.Actual)(hi:i≤ N)
local notation "M"=> S.side R i
variable (a b:Flavor 6) (s t:Axis)(g:su.Color)(e:ℤ)(u:Averaging)
local notation "φ"=> A.density i
local notation "G"=> marque (i:=i) A true a s
local notation "Γ"=>ms (i:=i) a A
local notation "X"=> foil φ (Gall.viaP A G u i)
local notation "Y"=> foil φ (Gall.viaP A Γ u i)
local notation "D!"=> Stew.delta (1:Grid M) s
local notation "J"=> onSpin M (gamma 0)
local notation "H"=> helm M
local notation "κ!"=> waveZ (c:=M) e s t
local notation "SX"=> foil φ (report A G u i 0)
local notation "SY"=> foil φ (report A Γ u i 0)
variable (hk:1 ≤ k)(hF:Chart k (foil (A.density i) (Gall.viaP A (marque (i:=i) A true a s) u i)) 1)(hY:Chart k (foil (A.density i) (Gall.viaP A (ms (i:=i) a A) u i)) 1)(hv:∀ᶠ V:Grid (S.side R i) in 𝓝 1, IsUnit (A.density i V))
private noncomputable def dims (x:Sheet M): Sheet M:=x -- macro S,R.Free
omit hA hi
private lemma δstill(x:Cray c)(r:ℝ)(hx:∀ i:Site c,x (i,s)=0): Stew.delta (kiln g (r • x)) s= Stew.delta (1:Grid c) s:=by
      have ht : Lat.shift 0 (kiln g (r • x)) s= Lat.shift 0 (1:Grid c) s:=by
           unfold Lat.shift; congr 1; funext i; unfold Lat.thread; rw [show kiln g (r • x) (i,s)= 1 from ?_]; rfl
           change Rudder.bird g (r*x (i,s))= 1; rw[hx, mul_zero]; simp[Rudder.bird]
      unfold Stew.delta; rw[ht]
private lemma moon (F:Density c 6)(v:Cray c)(h:Chart k F 1)(hk:1 ≤ k)(X':Lat.Fields c 6→ₗ[ℂ]Sheet c) : HasDerivAt (fun t:ℝ=> X' (F (kiln g (t • v)))) (X' (tent g F v)) 0:=by
       let L:= X'.toContinuousLinearMap.restrictScalars ℝ; let K:=F ∘ kiln g; have hc:=collinear g 0 F (k:=k) (by rw[kiln0]; exact h); have he: HasDerivAt (fun t:ℝ=>t • v) v 0:=by simpa using (hasDerivAt_id' (0:ℝ)).smul_const v
       have hv:HasFDerivAt K (tent g F) ((0:ℝ) • v):=by rw[zero_smul]; exact (hc.differentiableAt (by exact_mod_cast Nat.ne_of_gt hk)).hasFDerivAt
       have h:= L.hasFDerivAt.comp_hasDerivAt 0 (hv.comp_hasDerivAt 0 he); exact h
private noncomputable def wakeY (S T: Sheet c): Sheet c→ₗ[ℂ] Sheet c:= {
      toFun:=fun x=> S*(T*x)-(T*x)*S,map_add':=fun x y=>by simp_rw [mul_add,add_mul]; abel, map_smul':=fun z x=>by rw[Matrix.mul_smul,Matrix.mul_smul,Matrix.smul_mul,← smul_sub]; rfl }
include hA hi hk hF hY hv
lemma whirl (p:VerseL (S.side R i)) (hp:∀ v:Site M,p (v,s)=0): discs b (rub g X p) = if b=a then wakeY D! J (discs b (rub g Y p)) else 0:=by
       let P:Sheet M→ₗ[ℂ]Sheet M:= if b=a then wakeY D! J else 0; let Q:= discs (c:=M) b; have hm(x:Cray M)(hx:∀ i:Site M,x (i,s)=0): Q (tent g X x)=(P ∘ₗ Q) (tent g Y x):=by
             let V:(ℝ→Grid M):= fun z=> kiln g (z • x); have ht: Tendsto V (𝓝 0) (𝓝 1):=by
                  have h : Continuous (fun k:ℝ=> k • x):= continuous_id.smul continuous_const; have he:Tendsto (fun k:ℝ=> k • x) (𝓝 0) (𝓝 0):=by simpa using h.tendsto 0
                  exact (soonK g).comp he -- inference
             have he:(fun z:ℝ=>Q (X (V z)))=ᶠ[𝓝 0]fun z=> (P ∘ₗ Q) (Y (V z)):=by
                    filter_upwards [ht hv] with z h; change IsUnit (A.density i (V z)) at h; unfold Q; rw [Oren.inkX A hA a b s u (V z) hi h,show Stew.delta (V z) s=_ from δstill s g x z hx]; unfold P; split<;> rfl
             exact (moon g X x hF hk Q).unique ((moon g Y x hY hk (P ∘ₗ Q)).congr_of_eventuallyEq he) -- orientation
       let x:Cray M:=fun i=>(p i).re; let y:Cray M:=fun i=>(p i).im; have he: Q (rub g X p)=P (Q (rub g Y p)):=by
             change Q (tent g X x + Complex.I • tent g X y)= (P ∘ₗ Q) (_+ _); rw [map_add,map_add,map_smul,map_smul,hm _ (fun i=>by simp [x,hp]),hm _ (fun i=>by simp[y,hp])]
       change Q _=_; rw [he]; unfold P; split<;> rfl
variable (i' j':Fiber)(ht:s≠t)
local notation "G0"=> gamma (0:Axis)
include ht
omit hA hi hk hF hY hv ht in
private lemma aria(x y:Site c→ℂ)(S:Sheet c)(L':Spike):arityG c x y i' j' (Lat.onSpin c L'*S)= ∑ z:Fiber,wave L' i' z* arityG c x y z j' S:=by
       let C:= Lat.onSpin c L'; have hp(i j:Site c): QCD.Run.cell (C*S) i j= wave L'*QCD.Run.cell S i j:=by unfold C Lat.onSpin; rw [Bay.cell_ride_left]; rfl
       change (∑ v:Site c,∑ w:Site c,(star (x v)*y w)* QCD.Run.cell (C*S) v w i' j')= ∑ z:Fiber,_*(∑ v: Site c,∑ w:Site c,(star (x v)*y w)* QCD.Run.cell S v w z j'); conv_rhs=> simp only[Finset.mul_sum]; rw[sum_comm]
       refine sum_congr rfl fun v _=>?_ ; simp_rw[hp, Matrix.mul_apply,mul_sum]; rw[sum_comm]; apply sum_congr rfl; intro w _; exact sum_congr rfl fun i _=> mul_left_comm ..
set_option maxHeartbeats 600000 in
lemma ode : oracle2 e s t b i' j' g X= if b=a then (slope M e s s-slope M 0 s s)*(∑ z:Fiber, wave G0 i' z * oracle2 e s t b z j' g Y) else 0:=by
       let P:=arityG M (pars M e s) (pars M 0 s) i' j'; rw [ξverse2]; change P (discs b _)=_; rw [whirl A hA hi a b s g u hk hF hY hv _ (fun v=> by simp [waveZ,ht])]; split; next h=>
            unfold P wakeY; simp only [LinearMap.coe_mk,AddHom.coe_mk]; try change arityG M _ _ _ _ (D!*(J* (discs b (rub g Y (waveZ e s t))))-(J*(discs b (rub g Y (waveZ e s t))))*D!)=_; rw[map_sub,k_prev,k_next,← sub_mul,aria]; simp_rw[ξverse2]; rfl
       exact map_zero _
lemma leadT : river2 s t b i' j' g X=if b=a then (H⁻¹*(slope M 1 s s-slope M 0 s s))*(∑ z:Fiber, wave G0 i' z * oracle2 1 s t b z j' g Y) else 0:=by
      unfold river2; rw[ode A hA hi a b s t g 1 u hk hF hY hv _ _ ht,ode A hA hi a b s t g 0 u hk hF hY hv _ _ ht]; split<;> ring
end YM.Massive.Patria.Gall
#print axioms YM.Massive.Patria.Gall.leadT
