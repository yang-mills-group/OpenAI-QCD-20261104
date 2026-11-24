import YM.Gall.Trait
import YM.Gall.Coset
/-! Q and V gauge row reads. Defines linear gauge derivatives at weight exactly as real derivatives. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria.Gall
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.L2Operator TensorProduct Classical InnerProductSpace
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead Oriole Poised Poised.Beacon Kit Push.Local
variable {u t a D C v e s:ℝ}{c:Side}{n j d m r k p q w:ℕ}
local notation "Y★"=> Cray c
local notation "G★"=> Lat.Fields c 6
open QCD.Revolve TorusPCAC.Geometry Lining Lining.Ferry Lining.Temper Canvas
variable (P:BudgetPoint)(g:su.Color)(X:Labels.Taylor su 0)(Y:Labels.Taylor su 1)(T:TaperHol)
variable (k:Axis)(P₁ F F' F'' :Density c 6)
local notation "λℓ" U:arg => fling g T.T U
local notation "A𝕧"=> foil P₁ F
local notation "B!"=> trade (c:=c) (foil P₁ F) g
noncomputable abbrev stunt (k:Axis)(F:Density c 6): Density c 6:= (1/2:ℝ) • (march (step k) F - march (-(step k)) F)
lemma tradeF (t:ℝ)(h:Chart n F 1)(u v:Y★)(hn:2≤ n): trade (t • F) g u v=t • trade F g u v:=by
    let s:=shrub F; let V:=t • (ContinuousLinearMap.id ℝ ℂ); have hh: shrub (t • F)= V ∘ s:=funext fun U=>(((coef (∅:Finset (Pairs (Modes c 6)))).restrictScalars ℝ).map_smul t (F U))
    unfold trade; rw [hh,trailV g u v (V ∘ s) (show Chart n (V ∘ s) 1 from V.contDiff.contDiffAt.comp _ (shrub_p _ h)) hn,trailV g u v s (shrub_p F h) hn, Push.Local.left_linear V [ink g u,ink g v] (shrub_p _ h) hn]; rfl
lemma tradeSub (h:Chart n F 1)(hp:Chart n F' 1)(u v:Y★)(hn:2≤ n): trade (F-F') g u v=trade F g u v-trade F' g u v:=by
     have he : shrub (F-F')=shrub F-shrub F':=funext fun i=>(coef (∅:Finset (Pairs (Modes c 6)))).map_sub (F i) (F' i)
     unfold trade; rw [he, trailV g u v (shrub F-shrub F') (show Chart n (shrub F-shrub F') _ from (shrub_p F h).sub (shrub_p F' hp)) hn,trailV g u v _ (shrub_p _ h) hn, trailV g u v _ (shrub_p _ hp) hn]; let L:ℂ→L[ℝ]ℂ:= -ContinuousLinearMap.id ℝ ℂ; let p:=shrub F; let q:=shrub F'; change leftDerivs (p-q) _ _=_; rw [show p-q=p+(L∘q) from funext fun i=> sub_eq_add_neg ..,Push.Local.left_add [ink g u,ink g v] (shrub_p _ h) (show Chart n (L∘q) 1 from L.contDiff.contDiffAt.comp _ (shrub_p _ hp)) hn,Push.Local.left_linear L [ink g u,ink g v] (shrub_p F' hp) hn]; exact (sub_eq_add_neg ..).symm
set_option quotPrecheck false
local notation "Mk"=>Lattice.step (S:=ℤ) k
open Tawny Tawny.Cast.Perla.Fore
-- Read linear row function
lemma pages_c (u:Label d)(J:Labels.Jet su) : ContDiffAt ℝ (d:ℕ∞ω) (fun t:ℝ=>pages (scaleJet J (t^2)) u) 0:=by
       rw [show (fun t:ℝ=>pages (scaleJet J (t^2)) u) = _ from funext fun t=> (Gall.charge t u J).symm]; let L:SpinPol d→L[ℝ]ℂ:= (coef (∅:Finset (Pairs (SpinMode d)))).toContinuousLinearMap.restrictScalars ℝ; refine L.contDiff.contDiffAt.comp 0 (g:=⇑L) ?_ -- need h_d always proof
       change ContDiffAt ℝ _ (desired u.val J) _; rw [← funext (Display.observe J u.val)]; exact (Display.painted _ _ _).contDiffAt
def capote (d:ℕ) (J:Labels.Jet su): Label d→ₗ[ℂ]ℂ where
    toFun u:= (d.factorial:ℝ)⁻¹ • iteratedDeriv d (fun t:ℝ=>pages (scaleJet J (t^2)) u) 0
    map_add' u v:=by simp only [map_add]; rw [iteratedDeriv_fun_add (pages_c u J) (pages_c v J),smul_add]
    map_smul' v u:=by
        simp only [map_smul,RingHom.id_apply]; let V:= v • (ContinuousLinearMap.id ℝ ℂ); let f:=fun t:ℝ=>pages (scaleJet J (t^2)) u
        change (d.factorial:ℝ)⁻¹ • iteratedDeriv d (V∘ f) 0= _; rw[Display.clm_step _ _ _ (pages_c _ _)]; exact smul_comm (d.factorial:ℝ)⁻¹ v _
lemma valor8 (Q:Label 8) (h:Tally T 0 Q P₁ F)(hG:Along g X)(hD:Chart n A𝕧 1)(hp:8 ≤ n) : capote _ (leanY X 0) Q=(1/2:ℝ) • B! (λℓ X) (λℓ X):=by
    let A:= B! (λℓ X) (λℓ X); unfold capote; change (Nat.factorial 8:ℝ)⁻¹ • _=(1/2:ℝ) • A; rw [horn8 g T X 0 P₁ F Q h hG (along0 g 1) (hD.of_le (Nat.cast_le.mpr hp)) le_rfl]; exact inv_smul_smul₀ (by positivity) _
noncomputable def pan (X: Labels.Taylor su 0)(Y:Labels.Taylor su 1)(k:Axis): Label 8→ₗ[ℂ]ℂ:= capote 8 (leanY (X+radial Y k) 0) - capote 8 (leanY X 0)-capote 8 (leanY (radial Y k) 0)
lemma versa (Q:Label 8)(h:Tally T 0 Q P₁ F)(hh:‖g‖=1)(hX:Along g X)(hY:Along g Y)(hD:Chart n A𝕧 1)(hn:8 ≤ n): B! (λℓ X) (λℓ (radial Y k))=pan X Y k Q:=by
     unfold pan; rw [LinearMap.sub_apply,LinearMap.sub_apply]; let R:=radial Y k; have hp:Along g R:= radialG g Y _ hY hh
     rw[valor8 g (X+R) T P₁ F Q h (along_add g _ _ hX hp) hD hn, valor8 g X T P₁ F Q h hX hD hn, valor8 g R T P₁ F Q h hp hD hn,grow_flings]; let U: Y★:=λℓ X -- parser
     let M:Y★:=λℓ R; change B! U M= (1/2:ℝ) • B! (U+M) (U+M)-(1/2:ℝ) • B! U U-(1/2:ℝ) • B! M M; simp only [map_add, ContinuousLinearMap.add_apply]; rw [show B! M U=B! U M from pairs _ (collinear g 0 (shrub _) (show Chart n (shrub _) _ from (by rw[kiln0]; exact shrub_p _ hD))) (by omega) _ _]; module
-- normalized: no factors 40320/1843200
lemma surfaceT (hP:3 ≤ P.power)(hn:10 ≤ P.order)(hX:Along g X)(hY:Along g Y)(hh:‖g‖=1): ∃ C:ℝ,0 ≤ C ∧ ∀ (c:Side)(F G: Density c 6)(Q:Label 8)(R:Label 10)(v a:ℝ)(n j:ℕ), Tutor 0 P (foil G F) v n j a → Tally T 0 Q G F→ SungP F→SungP G→(∀ x:Cover,march x G=G)→ Tally T 0 R G (stunt k F)→ ‖capote _ (leanY X Y) R-pan X Y k Q‖ ≤ (c.val:ℝ)⁻¹*(C*a):=by
     obtain ⟨A,hA,hA'⟩ := shipped P g X Y T.T k Mk (show ballU _ _ 1 from Or.inl ⟨rfl,rfl⟩) hP (by omega); obtain ⟨D,hD,hD'⟩:=shipped P g X Y T.T k (-Mk) (show ballU _ _ (-1) from Or.inr ⟨rfl,rfl⟩) hP (by omega)
     refine ⟨(1/2:ℝ)*(A+D),by positivity,fun c F G Q R v a n j hv h hG he hp hR=>?_⟩; let f:= foil G F; let L(x):=foil G (march x F); let w:= foil G (stunt k F); let V:= trade f g; let u:Cray c:=λℓ X; let y: Cray c:=λℓ Y; let e:Cray c:=λℓ (radial Y k)
     have hm: w=(1/2:ℝ) • (L Mk-L (-Mk)):= funext fun x=>by change Ring.inverse (G x)*((1/2:ℝ) • (march Mk F x - march (-Mk) F x)) = (1/2:ℝ) • (Ring.inverse (G x)*march Mk F x - Ring.inverse (G x)*march (-Mk) F x); rw [mul_smul_comm, mul_sub]
     have hD(x):Chart P.order (L x) 1:=frugal _ _ (course x G F h.unit (hp _)) (marchC x f hv.smooth)
     have hD2:Chart P.order w 1:=by rw [hm]; exact contDiffAt_const.smul ((hD _).sub (hD _))
     have ht x:= cosmos g x G F h.unit (hp _) hv.smooth (show 2 ≤ P.order by omega) u y
     have hP : capote 10 (leanY X Y) R=(1/2:ℝ) • (V (floats Mk u) (floats Mk y)- V (floats (-Mk) u) (floats (-Mk) y)):=by
           have hx:=horn10 g T X Y G (stunt k F) R hR hX hY (show Chart 10 w 1 from hD2.of_le (Nat.cast_le.mpr hn)) le_rfl; change (Nat.factorial 10:ℝ)⁻¹ • iteratedDeriv 10 (fun t:ℝ=> pages (scaleJet (leanY X Y) (t^2)) R) 0= _; rw[hx,inv_smul_smul₀]; swap; · positivity
           change trade w g u y= _; rw[hm,tradeF g _ _ ((hD _).sub (hD _)) _ _ (show 2≤ P.order by omega),tradeSub g _ _ (hD Mk) (hD _) _ _ (by omega),ht,ht]
     have hF:= quirky f (treated G F he hG); have h1 := hA' c f _ _ _ a hv hF; have h2:= hD' c f _ _ _ a hv hF; rw [hP,←versa g X Y T k G F Q h hh hX hY hv.smooth (by omega)]; let p:= V (floats Mk u) (floats Mk y); let q:= V (floats (-Mk) u) (floats (-Mk) y)
     let z:=V u y; let w':=V u e
     change ‖(1/2:ℝ) • (p-q)-w'‖≤_; rw [show (1/2:ℝ) • (p-q)-w'=(1/2:ℝ) • ((p-(z+(1:ℝ) • w'))-(q-(z+(-1:ℝ) • w'))) from (by module),norm_smul,Real.norm_of_nonneg (by norm_num)]; exact (mul_le_mul_of_nonneg_left ((norm_sub_le ..).trans (add_le_add h1 h2)) (by norm_num : (0:ℝ)≤1/2)).trans_eq (by ring)
end YM.Massive.Patria.Gall
#print axioms YM.Massive.Patria.Gall.surfaceT
