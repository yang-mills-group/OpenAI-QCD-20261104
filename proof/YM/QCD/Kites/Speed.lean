import YM.QCD.Entr.Iris
/-! # Posterity speeds all symbols. Dilation continuity after. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Kites
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N k B n b j:ℕ}{p:BudgetPoint}{η u a r t w P q J δ z z' θ σ d A ε:ℝ}{i o:Site c}
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset Flume Pine YM.Next.Free Leaf LeafM Tee Garden Entr
variable {Γ:Silo c}{U:St c}
section factor
variable {D:Type*}[Fintype D][DecidableEq D]
noncomputable def engine (t:ℝ) (D:Type*) [Fintype D]: Alg D →ₐ[ℂ] Alg D := changeVars (Matrix.diagonal fun _=>(t:ℂ))
lemma ridesB (t:ℝ)(K: Matrix D D ℂ)(x:Alg D):changeVars K (engine t D x)=engine t D (changeVars K x):=by
    -- matrix multiplication
    unfold engine; rw [← AlgHom.comp_apply,← AlgHom.comp_apply,←change_mul,←change_mul]; congr 2; ext i j; simp [Matrix.diagonal_mul,Matrix.mul_diagonal]; ring
lemma fundW (x:Alg D)(t:ℝ)(i:Finset D): coef i (engine t D x)=(t:ℂ)^i.card*coef i x:=by
    change coef i (wscale (fun _=>t) x)=_; rw [Creek.wax,map_sum,sum_eq_single i]
    · rw [map_smul,map_smul, Grass.read]; simp only [prod_const, smul_eq_mul, mul_one]; rw [mul_comm]
    · intro j _ hj; rw [map_smul,map_smul,Grass.read_other _ _ hj.symm,smul_zero,smul_zero]
    simp
lemma makes (x:Alg D)(u v :ℝ): engine u D (engine v D x)=engine (u*v) D x:=by
    apply Stew.poster; intro s; simp_rw [fundW, Complex.ofReal_mul,mul_pow]; ring
lemma nominate (x:Alg D)(u:ℝ)(k:ℕ)(hp: x∈Grass.layer D k):engine u D x=(u:ℂ)^k • x:=by
    refine poster _ _ fun i=>?_ ; by_cases ht:i.card=k
    · rw [fundW,ht,map_smul]; rfl
    rw [map_smul,fundW,spectrum hp i ht, smul_zero,mul_zero]
lemma pitcher (L:Matrix D D ℂ)(x:Dirac D)(t:ℝ): disguise L (engine t (Pairs D) x)= engine t (Pairs D) (disguise L x):=by
    let p:= engine t (Pairs D); change _ = p _; rw [← write x]; simp only [map_sum,map_smul]; apply sum_congr rfl; intro i _; unfold p; rw [nominate (mono i) _ _ (homogeneous i),nominate (disguise L (mono i)) t i.card (exterior_layer _ (homogeneous i)),map_smul] -- simp p issue
lemma surfE (x:Dirac D)(t:ℝ): surf D (engine t (Pairs D) x)=engine t _ (surf D x):=by
    rw [← write x]; simp only [map_sum,map_smul,map_smulₛₗ]; refine sum_congr rfl fun i _=>?_ ; rw [nominate (mono i) t _ (homogeneous i),nominate (surf D (mono i)) t i.card (exterior_layer _ (cc_degree (homogeneous i))),map_smulₛₗ]; simp
end factor
local notation "V"=> EvenA c N
lemma dings (t:ℝ)(x: V)(S:Support c)(h:Gated S x): Gated S (wearK c N t x):=by
    change engine t (Keys c N) _∈_; -- spectrum 
    apply Cove.effects _ _ x.val h; intro i hi; unfold engine; rw [change_atom]; simp only [Matrix.diagonal_apply,ite_smul,zero_smul,Fintype.sum_ite_eq]; exact Subalgebra.smul_mem _ (Creek.marked _ _ hi) _
lemma moments (t a:ℝ)(o: Site c)(x:V)(ha:0 ≤ a)(ht:0≤t): Sen o a (wearK c N t x)= Sen o (t*a) x:=by
    unfold Sen; rw [Stew.plank,Stew.plank, pricesD _ ha,pricesD _ (mul_nonneg ht ha)]; refine sum_congr rfl fun i _=>?_ ; rw [show coef i ((wearK c N t x).val)=_ from fundW x.val t i,norm_mul,norm_pow, Complex.norm_real,Real.norm_of_nonneg ht]; unfold starch; ring
lemma quy (t a u:ℝ)(x:V)(ht:0<t)(ha:0<a)(he:t*a ≤ u): ‖token c N a (wearK c N t x)‖ ≤ ‖token c N u x‖:=by
    rw [skill,skill]; have hh y: ‖wearK c N y x‖= Creek.load (fun _=>y) x.val:=rfl; rw [show wearK c N a (wearK c N t x)= wearK c N (a*t) x from Subtype.ext (makes x.val a t), mul_comm a,hh,hh];
    rw [Creek.dry _ (fun _=> mul_pos ht ha),Creek.dry _ (fun _=> (mul_pos ht ha).trans_le he)]; apply sum_le_sum; intro i hi; rw [prod_const,prod_const]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); gcongr
lemma tastes (U:Sheet c)(r:ℝ)(F:ℕ): wearK c F r (paleF F U)=paleF F (r^2 • U):=by
    apply Subtype.ext
    have hp := nominate (form (Lat.copies F U)) r _ (Grass.form_two _); change engine r _ (form (Lat.copies F U))=_; rw [hp]; change _=(nozzle c F (r^2 • U)).val; rw [show nozzle _ _ _=r^2 • (nozzle c F U) from map_smul ((nozzle c F).restrictScalars ℝ) ..,← Complex.ofReal_pow]; rfl
lemma juke (t:ℝ)(w:ℝ): wearK c N t (baker c N w)=baker c N w:=by rw [gets]; exact (map_smul (songT t) w (1:V)).trans (congr_arg (fun x:V=> w • x) ((wearK c N t).map_one ..))
end YM.QCD.Kites
