import YM.QCD.Globe.Tao
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
open Nola Brick
lemma fleck (M: Sheet c)(i j: Modes c N):‖copies N M i j‖≤‖cell M i.1.1 j.1.1‖:=by rw [copies,Matrix.blockDiagonal_apply]; split; exact Cost.north (cell M i.1.1 j.1.1) i.1.2 j.1.2; rw [norm_zero]; exact norm_nonneg _
lemma bloomP (i j:Site c): Nola.tell ({i,j}:Support c) m=costS m i j:=by unfold Nola.tell costS;rw [Nola.pairR,add_comm] -- tell
variable {A:ℝ}
lemma radiantB (Y:Sheet c)(X:Ton id id m A Y)(p:Site c)(N:ℕ) : rayK locationP (copies N Y) m p≤ (Fintype.card (Brick.Note N:Type))^2*(2*A):=by
     let f i j:=costS m i j * ‖cell Y i j‖
     unfold rayK; rw [Fintype.sum_prod_type];
     let g(i j:Modes c N) := (if i.1.1=p then f i.1.1 j.1.1 else 0) + if j.1.1=p then f i.1.1 j.1.1 else 0
     apply le_trans (b:=∑ i:Modes c N,∑ j,g i j) (sum_le_sum (fun i _=> sum_le_sum fun j _=>?_))
     · simp_rw [mode_sum];
       have hp : ∀ i j:Brick.Note N,(∑ v:Site c,∑ w:Site c, g (placeQ v i) (placeQ w j)) ≤ 2*A:=by
           intro i j; change (∑ v:Site c,∑ w:Site c,((if v=p then f v w else 0)+if w=p then f v w else 0)) ≤ _; let h:= (∑ v:Site c, f v p); have he:h ≤ A:=by
                 have hx:= X.axR p; unfold Gan at hx; simp_rw [cell_flip,norm_star,id_eq,cost_symm p _] at hx; exact hx
           have ht:(∑ v:Site c, f p v)≤ A:= X.toR p; simp_rw [sum_add_distrib,sum_ite_eq', mem_univ,if_true]; rw [sum_comm (f:= fun v w=> if v=p then f v w else 0)]; simp_rw [sum_ite_eq',mem_univ,if_true]; unfold h at he; linarith
       apply le_trans (b:=∑ i:Brick.Note N,∑ j:Brick.Note N,2*A) (sum_le_sum (fun i _=>?_)); · simp only [sum_const, card_univ,nsmul_eq_mul]; exact le_of_eq (by ring)
       rw [sum_comm]; apply sum_le_sum; intro j _; exact hp i j
       
     have he(i j):0≤f i j:=mul_nonneg (cost_nn ..) (norm_nonneg _); have hp: poly locationP (.inr (i,j)) = {i.1.1,j.1.1}:=rfl
     have ht :=(mul_le_mul_of_nonneg_left (fleck Y i j) (cost_nn (m:=m) i.1.1 j.1.1)); dsimp only at *; rw [hp,bloomP, mul_comm (‖_‖)]
     change (if _ then costS m i.1.1 j.1.1 * _ else 0)≤ _; let w:= costS m i.1.1 j.1.1 * ‖copies N Y i j‖; unfold g
     have hv:0 ≤ f i.1.1 j.1.1:= he ..; change w≤f i.1.1 j.1.1 at ht; change (if _ then w else _) ≤ _; simp only [mem_insert,mem_singleton]; split_ifs with hf hj hl
     all_goals first | linarith only [ht,hv] | tauto
end YM.QCD.Globe
