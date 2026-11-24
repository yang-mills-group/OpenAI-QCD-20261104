import YM.Giles.Prom
import YM.Giles.Ports
/-! certifying point2 row with canonical gauges. Uniform probe limits from allowances. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria.Gall
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.L2Operator TensorProduct Classical InnerProductSpace
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead Oriole Poised Poised.Beacon Kit Push.Local
variable {u t a D C v e s σ :ℝ}{c:Side}{n l d m r k p q w:ℕ}
local notation "Y★"=> Cray c
local notation "G★"=> Lat.Fields c 6
open QCD.Revolve TorusPCAC.Geometry Lining Lining.Ferry Lining.Temper Canvas PCAC QCD.Entr.Goals
open Complex (exp I)
open Tawny Tawny.Cast.Rays
variable (T:TaperHol)(g:su.Color)(F P:Density c 6)(p:Flavor 6)(i j:Fiber)(a b:Axis)
local notation "Q"=> reed p p i j
local notation "Λ"=> (0:Multi 10)
local notation "N"=> ballast Λ Λ T.T
local notation "μ"=> mu2 a T.T
local notation "B"=>touch (su.colorMat g)
local notation "L"=>fling g T.T (legV g a b)
variable (x:Site c→Site c→ℂ)(φ:Site c→ℝ)
noncomputable def hit (p:Flavor 6)(F:Grid c→Lat.Fields c 6) (x:Site c→Site c→ℂ): Bundle:= ∑ i:Site c, ∑ j:Site c,x i j • (sift p i j (F 1))
lemma headsT (p:Flavor 6) (f:Grid c→Lat.Fields c 6) (x:Site c→Site c→ℂ)(i j:Fiber): hit p f x i j= reed p p i j x (f 1):=by unfold hit; simp_rw [Matrix.sum_apply,Matrix.smul_apply]; rfl --] -- placeholder
lemma boom (s:ℂ): hit p F (s • x)= s • hit p F x:=by
     unfold hit; simp_rw[Pi.smul_apply, Finset.smul_sum, smul_eq_mul, mul_smul]
lemma roll_p (h:Chart n F 1)(hp:SungP F)(hn:1 ≤ n): reed p p i j x (tent g F (glaze φ))=
        (B * hit p F (fun i j=> x i j*((-φ i:ℝ):ℂ))+hit p F (fun i j=> x i j*((φ j:ℝ):ℂ))*B) i j:=by
      let R(u v:Site c):= sift p u v; let V(u v:Site c):=R u v (F 1)
      have he(Z₀:G★): reed p p i j x Z₀=(∑ u,∑ v,x u v • (R u v Z₀):Bundle) i j:=(headsT p (fun _=>Z₀) x i j).symm
      rw [he]; unfold hit; apply congr_fun; apply congr_fun
      simp_rw [Finset.mul_sum,Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul, ← Finset.sum_add_distrib]; refine sum_congr rfl fun i _=>sum_congr rfl fun j _=>?_ ; rw [show R i j (tent g F (glaze φ))= _ from tell g _ i j φ hp h hn p, smul_add]; congr 1; all_goals rw [mul_smul, Complex.coe_smul]
noncomputable def chipK (v w:Multi d)(p:Flavor 6): Label d→ₗ[ℂ]Bundle:= {
    toFun:= fun x=>Tawny.gravel p p v w (juncoat x.val),map_add':=fun x y=>by change Tawny.gravel _ _ _ _ (juncoat (x.val+y.val))=_; rw[map_add,map_add],map_smul':=fun t x=>by change Tawny.gravel _ _ _ _ (juncoat (t • x.val))= t • _; rw[map_smul,map_smul] }
local notation "A"=>foil P F
local notation "w"=> ηR a b
lemma cluster (X:Label d)(h:Tally T 0 X P F)(u v:Multi d)(hj:spinWeight u+spinWeight v≤d) : hit p A (ballast u v T.T)= chipK u v p X:=by
     ext i j; rw [headsT]; exact strokeL T _ _ _ _ _ _ h _ _ hj
-- point2 gradient specific. split.Of scale 1/2.Pair multiplications sign.
variable (U:BudgetPoint)
noncomputable def fringe (a b:Axis)(p:Flavor 6)(i j:Fiber)(G:Bundle):Label 10→ₗ[ℂ]ℂ:= {
    toFun:=fun h=>
           let Z:=chipK (ηR a b) (0:Multi 10) p h
           let X:=chipK 0 (ηR a b) p h
           let Nh:= chipK (leadR a) (leadR b) p h
           (G*Z-Nh*G + (G*((-(1/2:ℂ)) • Z)+((1/2:ℂ) • X)*G)) i j
    map_add':= fun x y=>by dsimp only; rw [map_add,map_add,map_add]; simp_rw [smul_add,mul_add,add_mul]; simp only[Matrix.add_apply,Matrix.sub_apply]; abel
    map_smul':=fun s x=>by dsimp only; rw [map_smul,map_smul,map_smul,smul_comm (-(1/2:ℂ)) s,smul_comm (1/2:ℂ) s]; simp_rw[Matrix.mul_smul,Matrix.smul_mul, ← smul_sub, ← smul_add]; rfl }
noncomputable def awake2 (a b:Axis)(p:Flavor 6)(i j:Fiber)(g:su.Color): Label 10→ₗ[ℂ]ℂ:= fringe a b p i j (touch (su.colorMat g)) + tiltX p i j (leanY (legV g a b) 0)
lemma purseH (X:Label 10)(h:Tally T 0 X P F)(hC: Chart 10 A 1)(hA:SungP A)(hx:a≠b) : Q μ (tent g A (glaze (indexT b))) + Q N (tent g A (glaze (rimV a b)))= fringe a b p i j (touch (su.colorMat g)) X:=by
     rw [roll_p _ _ _ _ _ _ _ hC hA (by decide), roll_p _ _ _ _ _ _ _ hC hA (by decide)]; -- expand handles mul ℝ
     let τ:= T.T; let f(x y:Multi 10):= ballast (c:=c) x y τ
     have h1:(fun i j: Site c=> μ i j*((-(indexT b i):ℝ):ℂ))= f w Λ:=by funext i j; unfold mu2 f ballast Nw; rw [profile_N _ _ _ hx,profile_0]; unfold indexT τ; push_cast; ring
     have h2:(fun i j:Site c=> μ i j*((indexT b j:ℝ):ℂ))= (-1:ℂ) • f (leadR a) (leadR b):=by funext i j; unfold mu2 f; rw [Pi.smul_apply,Pi.smul_apply, smul_eq_mul]; unfold ballast Nw; rw[profile_L,profile_L]; unfold indexT τ; push_cast; ring
     have h3:(fun i j:Site c=> N i j*((-(rimV a b i):ℝ):ℂ))= (-(1/2:ℂ)) • f w Λ:=by funext i j; rw [Pi.smul_apply, Pi.smul_apply,smul_eq_mul]; unfold f ballast Nw rimV indexT τ; rw [profile_N _ _ _ hx]; simp only [profile_0]; push_cast; ring
     have h4:(fun i j:Site c=> N i j*((rimV a b j:ℝ):ℂ))= (1/2:ℂ) • f Λ w:=by funext i j; rw[Pi.smul_apply, Pi.smul_apply,smul_eq_mul]; unfold f ballast Nw rimV indexT τ; rw [profile_N _ _ _ hx]; simp only [profile_0]; push_cast; ring
     rw[h1,h2,h3,h4,boom,boom,boom,show hit p A (f w Λ)= _ from cluster T F P p X h _ _ (show spinWeight w + spinWeight Λ≤10 by rw [gradeH,gradeV]), show hit p A (f (leadR a) (leadR b)) = _ from cluster T F P p X h _ _ (show spinWeight (leadR a)+spinWeight (leadR b)≤10 by rw [gradeL,gradeL]), show hit p A (f Λ w)= _ from cluster T F P p X h _ _ (show spinWeight Λ+spinWeight w ≤10 by rw [gradeH,gradeV])]
     rw [neg_one_smul, Matrix.neg_mul, ←sub_eq_add_neg]; rfl
end YM.Massive.Patria.Gall
#print axioms YM.Massive.Patria.Gall.purseH
