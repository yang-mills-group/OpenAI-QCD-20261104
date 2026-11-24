import YM.QCD.Stew.Price
/-! # Sufficient non-scalar projection theorem. Gives map at every U,
FP Hard receiving additional Soft. Tax pre choices. Does not consume β change. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Stew
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N n z B D:ℕ} {w r a u t σ η A' K Q' y:ℝ}{p:BudgetPoint}{o:Site c}
open Revolve Flume Quarry AnalyticBridge.VerifiedReset Port Footprint
variable {ι:Type}(E:Gem c N ι)(b:Flavor N)
open Residual
lemma permits (h:Licence p σ a t E)(hx:0<t)(he:0≤σ) (U: Grid c): Summable (letters E p.threshold U):=by
    obtain ⟨f,hf,h⟩:=h.zone
    let L:= letters E p.threshold U; have hp i: ‖songT t (L i)‖ ≤ f i:=by
       unfold L letters; by_cases hn: Healthy p.threshold (E.addr i).support U
       · rw [masked_eq _ _ _ _ hn]; exact (shot (lens _) _ _ hx).trans ((h i).sizeU U hn)
       rw [masked_ne _ _ _ _ hn,map_zero,norm_zero]; exact (h i).travel
    have hh: Summable f:= Loom.sumRide _ _ _ hf (fun i=> (h i).travel) he
    exact ((songT t⁻¹).summable (Summable.of_norm_bounded hh hp)).congr fun i=> wit (L i) _ _ (inv_mul_cancel₀ hx.ne')
lemma crops (C:SampleX→Spike): |qMass C|≤ ‖C none‖ ∧ |qWave C| ≤ ‖C (.some (0,true))‖+‖C (.some (0,false))‖:=by
    constructor
    · exact (Complex.abs_re_le_norm _).trans (Cost.north ..)
    have hh b: ‖sineVal C 0 b‖≤ ‖C (.some (0,b))‖:= (Cost.north (Lat.gamma 0*C (.some (0,b))) (0,0) (0,0)).trans ((norm_mul_le ..).trans (mul_le_of_le_one_left (norm_nonneg _) (Lat.rotation_price (show Lat.gamma 0 ∈ unitary _ from ⟨by simp,by simp⟩))))
    exact (Complex.abs_re_le_norm _).trans ((norm_sub_le ..).trans (add_le_add (hh _) (hh _)))
theorem wealth (n m N:ℕ): ∃ K C:ℝ, 1 ≤ K ∧ 1 ≤ C ∧∀ (c:Side)(p:BudgetPoint)(σ t a u:ℝ),0 ≤ t→ t+1+1≤σ→2 ≤ p.B→p.order≤ n→p.power≤ m→1≤a →4 ≤ c.val→∀ (ι:Type)(E:Gem c N ι)(b:Flavor N), Crossing E→Licence p σ u a E→
     let Z:= dearth E b; let T:= lien E b p.threshold; let F:= till E b 0
     Crossing Z ∧ Licence p σ ((1+C)*Real.exp (81*σ)*u) a Z ∧ Purchases T p.threshold p.B t (Footprint.payment 1 (4*p.B+2) 0 1 (1+C) u t 81) a ∧ Quanta Z b∧
     a^2 * |qMass F| ≤ K*u∧ a^2 * |qWave F| ≤ 2*(K*u)∧∀ V, Summable (letters E p.threshold V)∧ Summable (letters Z p.threshold V)∧ HasSum (fun i=> T.mean i V) (Patron.total E p.threshold V-paleF N (backP F V)-Patron.total Z p.threshold V) :=by
    obtain ⟨C,hC,H⟩:= invoices n m N; obtain ⟨K,hK,h⟩:= preMoment; refine ⟨K,C,hK,hC,fun c p σ t a u he hv hB hn hm ha hp ι E b hP hL =>?_⟩
    intro Z T F
    obtain ⟨f,hf,hh⟩:= hL.zone; have ha':=zero_lt_one.trans_le ha; have hS i:= H _ b p a hn hm ha' ι E i _ (hh _); have hs:0≤σ:=by linarith
    have hh':E.Gather:= ⟨fun i=> (hh i).room,fun i=>(hh i).Borel,fun i=> (hh i).gated⟩
    have ht':Z.Gather:= ⟨fun i=> (hS i).2.2.1.room,fun i=>(hS i).2.2.1.Borel,fun i=> (hS i).2.2.1.gated⟩
    obtain ⟨h1,h2⟩:= cumulative E b hf hh (1+C) hs (by linarith) hB he hv
    have hy : Licence p σ _ a Z:=⟨(show ∃ v,_ from ⟨_,h1,fun i=>(hS i).2.2.1⟩)⟩; have hg:= diligent E b hf hh ha' hs hK h
    refine ⟨lunar E b hh' hP,hy,⟨Stew.auto E b hh' hP _,dues E b _ hh' ht' (fun i=> (hS i).1.Borel) (fun i=>(hS i).1.room) (fun i=>(hS i).1.gated),_,fun i U=>(shot (lens _) _ _ ha').trans ((hS i).2.2.2 U),h2⟩,emptyRide E b hp,?_,?_,?_⟩
    · apply (mul_le_mul_of_nonneg_left (crops F).1 (sq_nonneg _)).trans; exact hg _ _
    · apply (mul_le_mul_of_nonneg_left (crops F).2 (sq_nonneg _)).trans; rw [mul_add,two_mul]; exact add_le_add (hg _ 0) (hg _ 0)
    intro V; have hℓ:=permits Z hy ha' hs V; refine ⟨permits E hL ha' hs _,hℓ,?_⟩; let Y i:=(lien E b p.threshold).mean i V; apply ((readsV E b hf hh hP hs ha' V).sub hℓ.hasSum).congr_fun; intro i; exact (add_sub_cancel_right (Y i) (letters _ _ _ i)).symm
end YM.QCD.Stew
