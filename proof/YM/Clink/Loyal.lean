import YM.Clink.Lapis
import YM.Clink.Mote
import YM.Lapin.Bed
/-! Blossom unshifted allocation: activation charged only on valid masks, no all field derivatives for full envelope.Fin. Yield Flag.
-/
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
variable (a:Flavor 6)(o:Site c)(X:St c)(V:Grid c)
lemma strongK (h: StrongR o X p σ C C')(ht:0 < t): let G:= fingers 6^2*t^2
       Given o p t σ (G*C') (G*C) (bouquet a∘ X):=by
       intro G; obtain ⟨I,hI,Z,H,Hx,rfl⟩:=h; obtain ⟨f,g,b,hf,h,h'⟩:= H.book; have hG:0≤G:=mul_nonneg (sq_nonneg _) (sq_nonneg t); let Y(i:I):= (Z i).R
       have hh (k:I→ℝ)(t:ℝ)(h:Ac.Hit Y p.B k σ t):Ac.Hit Y p.B (fun i:I=> G*k i) σ (G*t):=by
         intro i; convert budget_scale hG (h i) using 1; funext j; split; next hp=> exact mul_assoc ..
         next=> exact (mul_zero _).symm
       refine ⟨I,hI,Y,(fun i=>bouquet a∘(Z i).val),_,_,?_,fun i=> sunup a (Z i) (hf _),Hx,fun i=> textile a (Z i) (hf _) ht o (Hx i),hh g C' h',hh f C h,fun i V=>?_⟩
       · funext V; rw[Finset.sum_apply]; dsimp only [Function.comp_apply]; rw[Finset.sum_apply,map_sum] -- dsimp sums both
       let z:= (Z i).f V; have he: ‖z‖≤ f i:= (le_mul_of_one_le_right (norm_nonneg _) (one_le_pow₀ (by simp))).trans ((hf _).global V); exact (milk a _ (hf _) ht z).trans (mul_le_mul_of_nonneg_left he hG)
local notation "D"=> punct o
variable {I:Type}(x:Axis)(d:Step)(W:I→ Bloom k)(hW:Fractal W η C)
noncomputable def startZ(o: Site c)(w:Walk):= o-wrap c (stop (0:Cover) w)
lemma castP(w:Walk): stop (startZ o w) w=o:=by simp[wrap_stop,startZ]
local notation "U"=> wild W ξ c
local notation "Pz"=> (fun V:Grid c=> leg 0 V d)
lemma tagsL (he:0<η)(hp:0<k)(b n:ℕ)(hv:0≤σ) : ∃ B:ℕ,∃ C Q δ:ℝ,1 ≤ Q∧0<δ∧0 ≤ C∧∀ (ξ:ℝ),0<ξ→ξ≤1→∀ (c:Side)(p: BudgetPoint), p.threshold≤δ*ξ→p.power≤b→p.order ≤ n→ B ≤ p.B →∀ (I:Type) (W:I→Bloom k) (r:ℝ)(H: Fractal W η r) (o:Site c)(d:Step),StrongR o (fun V:Grid c=>wild W ξ c V*(punct o*leg 0 V d)) p σ (C*r*ξ) (Q*C*r*p.threshold) ∧ StrongR o (fun V:Grid c=> (leg 0 V d* punct o)*wild W ξ c V) p σ (C*r*ξ) (Q*C*r*p.threshold):=by
       obtain ⟨B,C,Q,δ,hp',hδ,hC,h⟩:= subsidy η σ b n k he hv hp; refine ⟨B,C,Q,δ,hp',hδ,hC,fun ξ hξ hz c p hθ ht hN hb I W r H o d=>?_⟩
       let y(V:Grid c):=leg 0 V d; let v(V):= punct o * y V; let A(V):= y V*punct o; let u:= startZ o [d]; let x(s:I):=startZ o (W s).tail
       constructor
       · have hh(s:I):stop (x s) (W s).tail=o:=castP ..
         have h0(s:I): o∈ nursery (W s) [] ((W s).tail++[d]) (x s):=by
                refine mem_union_right _ (List.mem_toFinset.mpr (?_)); rw [show stop (x s) []=x s from rfl]; -- proof visits_append.
                have ht (l:Walk)(b:Site c) : stop b l∈ Lattice.visits b (l++[d]):=by induction l generalizing b with| nil=>simp [stop,Lattice.visits]|cons a l ih=> exact List.mem_cons_of_mem b (ih (b+a.vec))
                exact (hh s) ▸ ht (W s).tail (x s)
         refine Eq.mp (congr_arg (fun F=> StrongR o F p σ (C*r*ξ) (Q*C*r*p.threshold)) ?_) (h ξ hξ hz c p hθ ht hN hb o I W r H (fun _=>[]) (fun i=>(W i).tail++[d]) x (by intro i; simp) h0); funext V; unfold wild; rw [← ((earns V H hξ hz he).of_norm).tsum_mul_right]; exact tsum_congr fun i=> (kef o _ _ _ _ _ (hh i)).symm
       have h0: stop u [d]=o:=castP ..
       have hQ(s:I): o∈nursery (W s) [d] (W s).tail u:= h0 ▸ (nucleus (W s) [d] _ u).2.1 -- notation binder.ty
       refine Eq.mp (congr_arg (fun F=> StrongR o F p σ (C*r*ξ) (Q*C*r*p.threshold)) ?_) (h ξ hξ hz c p hθ ht hN hb o I W r H (fun _=> [d]) (fun i=>(W i).tail) (fun _=>u) (by intro i; simp) hQ); funext V; unfold wild; rw [← ((earns V H hξ hz he).of_norm).tsum_mul_left]; apply tsum_congr; intro i; rw[h0]; exact (berg o u _ _ _ _ h0).symm
end YM.QCD.Entr.Meridian
#print axioms YM.QCD.Entr.Meridian.tagsL
#print axioms YM.QCD.Entr.Meridian.strongK
