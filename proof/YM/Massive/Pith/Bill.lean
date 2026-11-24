import YM.QCD.High.Stroll
import YM.Massive.Pith.Jaw
import YM.Massive.Lime.Leaves
/-! # the lead input mass term (the designated mark owner), pair projection through logarithm and principal naked S-copy mean. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Finch
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun Kites
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {I J V:Type}{c f:Side}{N n:ℕ}
open Animals
open Flume Orbit Quarry Folding Further.PhysicalPeriodLimitF933 Macrame PhysicalNext.Repeat Deck Meadow
open Pressure ConnectedActivityE6 Blaze King Push.Uniform
open Brick Dust Grove Entr YM.Next.Free Bloch Laurent QCD.Free
variable {t s τ u :ℝ}{j k:ℕ}{B:BudgetPoint}
variable (o:Site c)(a: Flavor N)(X:Crate c N)


-- exterior pure grade and peroxide log. Need hp only for `Log.sumable`. Use mass form nil even so powers off grade3. works for high twists via grade argument.
open QCD.Pith Massive.Log
variable {a' C:ℝ} (N:ℕ) (A:Kit.Rail f c)
variable {D K : Type}[Fintype D][Fintype K]
lemma AppleP {F: ℕ} (x: Crate f F) : Stew.panel 2 (apple A F x)=apple A F (Stew.panel 2 x):=by
   rw [← write x]; simp only [map_sum,map_smul]; refine sum_congr rfl fun i _=>?_ ; rw [past _ _ (homogeneous _),past i.card 2 (show apple A F (mono i) ∈ layer _ i.card from exterior_layer _ (homogeneous i))]; split; · rfl
   rw [map_zero]
noncomputable def stripe (b:Flavor N) (x:Sheet f) : FormN f N:=Matrix.blockDiagonal (fun i:Flavor N=> if b=i then x else 0)
lemma grapes (X: Flavor N→Sheet f): apple A N (form (Matrix.blockDiagonal X))= form (Matrix.blockDiagonal fun i: Flavor N=> railDay A * X i * A):=by
    change adapter (choir N A) (choir N (railDay A))ᵀ _=_
    rw [Grass.form_map, Matrix.transpose_transpose]; unfold choir; rw [← Matrix.blockDiagonal_mul,← Matrix.blockDiagonal_mul]; apply congr_arg; apply congr_arg; exact funext fun i=> (Matrix.mul_assoc ..).symm
lemma leadsP (b:Flavor N)(p:Sheet f) (X: EvenA f N) (h:Stew.panel 2 X.val=form (stripe N b p)) (m:Flavor N): tierL (c:=c) m (Dust.bill A N X)= if b=m then railDay A * p * A else 0:=by
   ext i j; change grasp (apple A N X.val) _ _= _; rw [← breast,AppleP,h, stripe,grapes, gravid]; rcases eq_or_ne b m with h|h <;> simp [Matrix.blockDiagonal_apply,h] -- grapes stripe defeq rewrite?
-- to watch aggregate via Rent.E field all-sites sum. Steiner. Fermion order Ln. Pair sign.
lemma eachP (b: Flavor N)(z: ℝ)(i:Site f) (g:EvenA f N)(h : (unitL b z i)=g): Stew.panel 2 g.val= form (stripe N b (localX i ((z:ℂ) • 1))):=by unfold stripe; rw [← h,show (unitL ..).val=_ from Pith.pure ..]; exact (past 2 2 (Grass.form_two _)).trans (if_pos rfl)
open YM.QCD.High.PrismT
lemma visibleLog (x:EvenA c N)(he:mud x=0)(h:‖x‖<1): panel 2 (Massive.Log.log x).val=panel 2 x.val:=by
    let p:EvenA c N →L[ℝ] EvenA c N := ContinuousLinearMap.restrictScalars ℝ (LinearMap.toContinuousLinearMap (Stew.stage 2)); have h₁:= p.hasSum ((Massive.Log.afford h).of_norm.hasSum)
    let v(n:ℕ):= Massive.Log.c n; change HasSum (fun i=> p (v i • x^i)) (p (∑' i,v i • x^i)) at h₁; have hp:p (Massive.Log.log x)= p x:=by
       rw [Massive.Log.log_eq, ← h₁.tsum_eq, tsum_eq_single 1] -- syntax
       · rw [show v 1=1 from by norm_num [v,Massive.Log.c],pow_one,one_smul]
       intro i hi; cases i with
       | zero=> rw [show v 0=0 from by norm_num [v,Massive.Log.c],zero_smul,map_zero]
       | succ i=> rw [map_smul,show p _ = 0 from ?_,smul_zero]; apply Subtype.ext; refine poster _ _ (fun y=>?_); change coef y (panel 2 _)=coef y 0; rw [angel,map_zero]; 
                  split; next he'=> rw [pow_succ]; exact lossM y he'.le _ _ (held _ _ he (by omega)) he
                  next _=> rfl
    exact congr_arg Subtype.val hp
-- log projects pair exactly, and does not create from powers of any scalarless EvenA. layer argument or meter_is. inspect algebra
lemma onShelf (m: Flavor N→ℝ) (i:Site f × Flavor N→ EvenA f N)(b:Flavor N) (h:∀ u:Site f×Flavor N, Stew.panel 2 (i u).val=form (stripe N u.2 (localX u.1 ((m u.2:ℂ) • 1)))) :
    (∑ u, planeW c t b (Dust.bill A N (i u)))= t^2*((Fintype.card (Site c):ℝ)*(m b * flagW (railDay A*A))) :=by
    let F(Q:Sheet c):= t^2 • (stow Q).re; let L: Sheet c →L[ℝ]ℝ:= t^2 • Complex.reCLM.comp ((stowL c).restrictScalars ℝ); let Z u:= tierL b (Dust.bill A N (i u))
    have hp : (∑ u, Z u)= (m b) • (railDay A*A):=by
       rw [Fintype.sum_prod_type]; simp_rw [Z,leadsP N A _ _ _ (h _) b]; let M:=((m b:ℂ) • (1:Spike)); have he (i:Site f): (∑ u:Flavor N,(if u=b then railDay A*localX i ((m u:ℂ) • 1)*A else 0))= railDay A* localX i M*A:= by rw [sum_ite_eq',if_pos (Finset.mem_univ _)]
       -- remove
       simp_rw [he]; rw [← Matrix.sum_mul,← Matrix.mul_sum];
       unfold M; simp_rw [pineS]; rw [← Finset.smul_sum,Stew.volley 1 f,on_spin_one,Matrix.mul_smul,Matrix.mul_one,Matrix.smul_mul]; exact Complex.coe_smul ..
    change (∑ u,L (Z u))=_
    rw [← map_sum,hp, map_smul]; change m b * (t^2*((stow (railDay A*A)).re))= _; rw [far]; ring
end YM.QCD.Finch
#print axioms YM.QCD.Finch.onShelf
