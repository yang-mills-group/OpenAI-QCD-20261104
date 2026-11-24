import YM.QCD.Globe.Coil
import YM.QCD.Nola.Wheat
import YM.QCD.Nola.Arch
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Globe
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset Flume Pine YM.Next.Free Leaf LeafM Tee Garden Entr Kites
variable {f c:Side}{j k m N:ℕ}{S:Flight j k} {h:f.val=c.val*S.L.val}{p:BudgetPoint}
open Fork Nola
variable {D E:Type*}[Fintype D][Fintype E][DecidableEq D][DecidableEq E]{u:D→Site c}{v:E→Site c}{a b t:ℝ}{X Y:ArrayL D E}
lemma Ton.pow {X:ArrayL D D}(h:Ton u u m a X)(he:0≤a)(n:ℕ): Ton u u m (a^n) (X^n):=by
    induction n with
    | zero=> rw [pow_zero,pow_zero]; exact Ton.one
    | succ n ih=> rw [pow_succ,pow_succ]; exact ih.op h (pow_nonneg he _) he
lemma Gan.entry (i:D)(j:E): costS m (u i) (v j)* ‖cell X i j‖ ≤ Gan u v m X i:= single_le_sum (fun k _=> mul_nonneg (cost_nn (m:=m) (u i) (v k)) (norm_nonneg _)) (mem_univ j)
lemma Cent.bike (h:Cent u v m a X)(i:D× Lat.Fiber)(j:E× Lat.Fiber): ‖X i j‖ ≤ a:=by
    apply (Cost.north (cell X i.1 j.1) i.2 j.2).trans; refine le_trans (le_mul_of_one_le_left (norm_nonneg (cell X i.1 j.1)) (cost_one (m:=m) (u i.1) (v j.1))) ((Gan.entry ..).trans (h _))
lemma Cent.empty (u:D → Site c)(v:E→Site c) : Cent u v m 0 (0:ArrayL D E):=fun i=> (by change _≤ (0:ℝ); simp only [Gan, show ∀ j,cell (0:ArrayL D E) i j=0 from fun _=> rfl,norm_zero,mul_zero,sum_const_zero,le_refl])
lemma Ton.empty : Ton u v m 0 (0:ArrayL D E):=by
    refine ⟨Cent.empty _ _,by rw [Matrix.conjTranspose_zero]; exact Cent.empty _ _⟩
-- partial sums proof.Neumann any Ton small.M
lemma Ton.near {X:ArrayL D D}(h:Ton u u m a (1-X))(he:0 ≤ a)(ht:a<1): IsUnit X.det ∧ Ton u u m (1-a)⁻¹ X⁻¹:=by
    let Y:=1-X; let Z(i:ℕ): ArrayL D D:= Y^i; have hh : HasSum (fun i:ℕ=>a^i) (1-a)⁻¹:= hasSum_geometric_of_lt_one he ht
    have hp(i): Ton u u m (a^i) (Z i):= h.pow he i
    have hz : Summable Z:=by
        have he (i:D×Lat.Fiber):Summable fun t:ℕ=> (Z t) i:=by
           apply Pi.summable.mpr; intro j; exact Summable.of_norm_bounded hh.summable fun t=> Cent.bike (hp t).toR i j
        exact Pi.summable.mpr he
    let f(n:ℕ):= ∑ i∈range n, Z i; let A:=∑' i,Z i; have hv:Tendsto f atTop (𝓝 A):= hz.hasSum.tendsto_sum_nat
    have he' : X*A=1:=by
        have hX(n:ℕ): X*f n=1-Z n:=by
           induction n with
           | zero=> simp [f,Z]
           | succ n ih=> rw [show f (n+1)=f n+Z n from sum_range_succ Z n, Matrix.mul_add,ih]; unfold Z; rw [pow_succ']; nth_rw 1 [show X=1-Y from (by unfold Y; abel)]; noncomm_ring
        have ht': Tendsto (fun i=>1-Z i) atTop (𝓝 (1-0)):= tendsto_const_nhds.sub hz.tendsto_atTop_zero;
        rw [sub_zero] at ht'; exact tendsto_nhds_unique_of_eventuallyEq (tendsto_const_nhds.mul hv) ht' (Eventually.of_forall hX)
    have hA:IsUnit X.det:= Matrix.isUnit_det_of_right_inverse he'
    refine ⟨hA,?_⟩; have hZ:X⁻¹=A:= Matrix.inv_eq_right_inv he'; rw [hZ]; apply Ton.limit f atTop hv; intro i
    have h' : Ton u u m (∑ k∈range i,a^k) (f i):=by
        induction i with
        | zero=>simp only [f,range_zero,sum_empty]; exact Ton.empty
        | succ i ih=> exact (by rw [sum_range_succ, show f _=_ from sum_range_succ Z i]; exact ih.add (hp i))
    exact h'.up ((hh.summable.sum_le_tsum (range i) fun i _=> pow_nonneg he i).trans_eq hh.tsum_eq)
end YM.QCD.Globe
