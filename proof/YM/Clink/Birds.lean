import YM.Clink.Loyal
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.QCD.Entr.Meridian
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator Kronecker
variable {c:Side}{N k B n b j:ℕ}{p:BudgetPoint}{η u a r t w P q J δ z z' θ σ C C' α α' ξ M:ℝ}{i o: Site c}
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset Flume Pine YM.Next.Free Leaf LeafM Tee Garden
open WardBin.Lies Eyrie Rudder Massive.PCAC
open MassiveQCD MassiveQCD.Sample.Basal.WindowU
variable (a:Flavor 6)(o:Site c)(x:Axis)(X:St c)(V:Grid c)
local notation "D"=> punct o
local notation "d"=> delta V x
lemma θB : sourceT a o x X V= bouquet a ((X V)*(D*d)-(d*D)*(X V)) :=by
        let P:= copies 6 (X V); let W:= (X V); rw [sourceT]; apply congr_arg cream; change P *(keel o x a V)-(keelB o x a V)*P = (((X V)*(D*d)-(d*D)*(X V)) ⊗ₖ Massive.PCAC.spot a a)
        unfold keel keelB; rw [←cashD o 6,show P=W ⊗ₖ 1 from Sway.choir_in .., show copies 6 (D)= D ⊗ₖ 1 from Sway.choir_in ..]; rw [← Matrix.mul_kronecker_mul,← Matrix.mul_kronecker_mul (delta V x) (punct o),← Matrix.mul_kronecker_mul,← Matrix.mul_kronecker_mul]; simp -- Matrix.sub_kronecker
        exact (map_sub (capsΛ a) _ _).symm
lemma joined' (Y:St c) : sourceT a o x (X+Y)=sourceT a o x X+sourceT a o x Y:=by funext V; rw[Pi.add_apply,θB,θB,θB,Pi.add_apply, Matrix.add_mul, Matrix.mul_add]; simp only [map_sub,map_add]; abel
private lemma minusX (X Y:Grid c→EvenA c 6)(hp:Given o p t σ C C' X)(hq:Given o p t σ C C' Y): Given o p t σ C C' ((2:ℂ)⁻¹ • (X-Y)):=by
       have hx:=Given.units _ o (Given.plies _ o hp _ (Given.units _ o hq (-1))) ((2:ℂ)⁻¹); norm_num at hx ⊢; convert hx using 1 <;> first | rfl | apply congr_arg; abel| (solve|ring)|(solve|module) -- inspect
variable (w:ℝ)(h:∀ s:Step,StrongR o (fun V=>X V * (punct o* leg 0 V s)) p σ C C'∧ StrongR o (fun V=> (leg 0 V s* punct o)*X V) p σ C C')
include h
local notation "G"=> fingers 6^2*t^2
lemma epochQ (hv:0<t): Given o p t σ (2*(G*C')) (2*(G*C)) (sourceT a o x X):=by
       let f(s:Step)(V):=X V*((D)*leg 0 V s); let g(s:Step)(V):=(leg 0 V s* D)*X V
       let k:=posDir x; let j:=negDir x; let F(s):= bouquet a ∘ f s; let Q(s):= bouquet a ∘ g s
       let z:=(2:ℂ)⁻¹; have ht: sourceT a o x X= z • (F k-F j)- z • (Q k-Q j):=by
            funext V; simp only [θB,Stew.delta]; rw [Matrix.mul_smul,Matrix.mul_smul,Matrix.smul_mul,Matrix.smul_mul, Matrix.mul_sub,Matrix.mul_sub,Matrix.sub_mul,Matrix.sub_mul,map_sub,map_smul,map_smul,map_sub,map_sub]; rfl
       rw [ht,sub_eq_add_neg (z • _),←neg_one_smul ℂ (z • (Q k-Q j)),two_mul,two_mul]; have hW(s): Given o p t σ (G*C') (G*C) (F s) :=strongK a o _ (h s).1 hv; have hQ(s): Given o p t σ (G*C') (G*C) (Q s) :=strongK a o _ (h s).2 hv; apply Given.plies _ o (minusX _ (F k) (F j) (hW k) (hW j)); convert Given.units _ o (minusX _ (Q k) (Q j) (hQ k) (hQ j)) (-1) using 1<;> simp
omit h
lemma crisp (hk:0<k)(hr:0<η)(P:ℝ)(hs:0≤σ)(n b:ℕ): ∃ C:ℝ, ∃ B:ℕ,∃ δ:ℝ,0 ≤ C∧0<δ∧∀ (V:Offer k η P)(c:Side)(p:BudgetPoint), p.power ≤ b→ p.order ≤ n→ B ≤ p.B → ∀ ξ:ℝ,0<ξ→ ξ ≤1→p.threshold≤δ*ξ→∀ t:ℝ,0<t→∀ (a:Flavor 6)(o:Site c)(x:Axis), Given o p t σ (C* t^2 * p.threshold) (C*t^2*ξ) (sourceT a o x (LeafM.wild (frosting V.W) ξ c)):=by
        let σ':=η/(1+(k:ℝ)); have hp:0<σ':=div_pos hr (by positivity)
        obtain ⟨B,C,Q,δ,hQ,hδ,hC,H⟩:= tagsL hp hk b n hs
        let T:= (Real.exp (η*(2*k))*P); let F:= fingers 6^2; let J:= 2*(F*(Q*C*|T|)); have hv : 0≤J:=by unfold J F; positivity
        refine ⟨J,B,δ,hv,hδ,fun V c p hV hO hW ξ hξ he h t ht a o x=>?_⟩; have hx: Fractal (frosting V.W) σ' T:= coined _ hp.le V.price (by unfold σ'; field_simp; simp)
        have ht0:0≤ T:=(tsum_nonneg (fun i=> (Bloom.price_nn _).trans ((frosting V.W i).paidUp hp.le))).trans hx.bill; let U:= wild (frosting V.W) ξ c; apply Given.adoptsA _ _ (epochQ a o x U (fun s=>H ξ hξ he c p h hV hO hW _ _ _ hx o s) ht) -- hp var hParam order H o? inspect H
        · unfold J F; rw [abs_of_nonneg ht0]; exact le_of_eq (by ring)
        unfold J F; rw [abs_of_nonneg ht0]; apply le_trans (b:=2*(fingers 6^2*t^2*(Q*C*T*ξ))) ?_ (le_of_eq (by ring)); have hZ : C ≤ Q*C:=le_mul_of_one_le_left hC hQ; gcongr
end YM.QCD.Entr.Meridian
#print axioms YM.QCD.Entr.Meridian.crisp
#print axioms YM.QCD.Entr.Meridian.θB
