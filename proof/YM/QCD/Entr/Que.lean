import YM.QCD.Entr.Dealt
import YM.Push.ABSOLUTE_SUMS.Reserves
import YM.Next.SCHEDULE.Resize
/-! # scalar pricing tilts unmasked and masked. Hull-local. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Entr
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N k B n:ℕ}{p:BudgetPoint}{η u a r t w P q J δ z:ℝ}{i j o:Site c}{X:Support c}
open Revolve Villa Port
variable {Γ:Silo c}{A: BankP c}{U:St c}
lemma debtT (d:Tick c)(x:Bundle)(hd: d.1∈ X)(hh:d.2.1∈X)(hA:∀ i∈X,separation i o≤n)(hp:0<a) (N:ℕ): Sen o a (paleF N (Stew.block d.1 d.2.1 x)) ≤ (1+n:ℝ)^2*a^2*fingers N^2 * ‖x‖:=by
    let M:= x; let i:=d.1; let j:=d.2.1
    have hf: jacket (Modes c N) (Lat.copies N (Stew.block i j M)) a ≤ a^2*fingers N^2* ‖M‖ :=by
       let Z:= Lat.copies N (Stew.block i j M); let w x y:= if x=i ∧ y=j then ‖M‖ else 0
       have he x y : 0 ≤ w x y:=ite_nonneg (norm_nonneg _) le_rfl
       have h(i':Modes c N)(j':Modes c N): ‖Z i' j'‖≤ w (headF i') (headF j'):=by
          unfold Z copies; rw [Matrix.blockDiagonal_apply]; split
          next hp=> unfold w; change _ ≤ if i'.1.1=i ∧ j'.1.1=j then ‖M‖ else 0; rw [Stew.block,Matrix.of_apply]; split
                    next ht=> exact Cost.north ..
                    next ht=> rw [norm_zero]
          next hp=> rw [norm_zero]; apply he
       unfold jacket
       apply (mul_le_mul_of_nonneg_left (paddleB (F:=N) 0 (∅:Support c) 0 (fun i j=> ‖Z i j‖) w h) (sq_nonneg _)).trans; rw [mul_assoc, show (∑ i,∑ j,w i j)=‖M‖ from ?_]
       unfold w; rw [sum_eq_single i]; · simp
       · intro x _ hx; simp [hx]
       simp
    refine (senCamp X hA _ hp (padBl _ _ M hd hh)).trans ?_
    exact ((mul_le_mul_of_nonneg_left ((Port.fauna _ hp).trans hf) (by positivity : 0 ≤ (1+(n:ℝ))^2)).trans_eq (by ring))

def fertile (Q: Tick c):Prop:=Q.1 ∈ Q.2.2 ∧ Q.2.1∈ Q.2.2
lemma debtless (h: Run.Pack id id η δ B U q Γ A)(d:Tick c)(V: Grid c)(hh: ¬fertile d)(ht:0<η): fareP Γ d V=0:=by
    obtain ⟨_,hp,hP,hS,H⟩:= h.crop d.1 d.2.1 d.2.2
    exact norm_le_zero_iff.mp ((hS _ (citizenship _ ht V)).trans_eq (by_contra fun he=> hh (hp he)))
noncomputable def silos (A:BankP c)(d:Tick c):ℝ:=A d.1 d.2.1 d.2.2
def diameterQ (B:ℕ)(X:Support c):=coverNumber B X*(4*B+2)+2*B
def tribute (B R n:ℕ)(X:Support c):ℝ := (1+(diameterQ B X:ℝ))^(2+R*n)
lemma need (h:Run.Pack id id η δ B U q Γ A)(d:Tick c):0 ≤ silos A d:= (h.crop ..).1
lemma asset (B R n N:ℕ): ∃ C:ℝ,0≤C∧∀ (c:Side)(A:BankP c)(Γ:Silo c)(η δ a q:ℝ)(U:St c), Run.Pack id id η δ B U q Γ A →∀ p:BudgetPoint,p.order≤n→p.power≤R→p.threshold ≤ η→ 0<a→∀ d:Tick c, fertile d → ∀ o∈d.2.2,
    let f(V:Grid c):=paleF N (pairQ Γ d V); let X:= C*a^2*silos A d*tribute B R n d.2.2
    Woven o d.2.2 p a f X ∧∀ V, Sen o a (f V)≤ X :=by
    obtain ⟨C,hc,h⟩:= drops B n R; refine ⟨fingers N^2*C, by positivity,fun c A Γ η δ a q U he p hP hp ht hz d hd o hh=>?_⟩; intro f X
    let i:=d.1; let j:=d.2.1; let Y:=d.2.2; let u:=Γ i j Y; let L:=((nozzle c N).comp (blockL i j)).restrictScalars ℝ; have hQ:= he.crop i j Y; have hy:=p.threshold_pos.trans_le ht; let g V:= L (u (settled V)); have hF (V:Grid c) l (he :List.length l ≤p.order)(ht':∀ x∈l,p.dirBound o x): Sen o a (leftDerivs g l V) ≤ X:=by
       unfold g; change Sen _ _ (leftDerivs (L ∘ (u ∘ settled)) _ V)≤_; rw [Push.Local.left_linear L l (milady hQ hy V p.order) he]
       let D:= diameterQ B Y
       apply (debtT d _ hd.1 hd.2 (n:=D) (fun i hi=> Corona.extent Y B hi hh) hz N).trans; apply (mul_le_mul_of_nonneg_left (h c p u η (silos A d) i j o Y hh hp hP ht hQ l he ht' V) (by positivity : 0 ≤ (1+(D:ℝ))^2*a^2*fingers N^2)).trans_eq; change _=X; unfold X tribute D diameterQ Y ; ring -- potential D order
    have hM:= need he d; refine ⟨⟨fun V U h=> congr_arg L (hQ.2.2.2.2.1 _ _ h),fun _=> padBl _ _ _ hd.1 hd.2, fun V hv=> L.contDiff.contDiffAt.comp 0 (milady hQ hy V p.order), fun _ _=> hF _,(L.continuous.comp (breeze hQ hy)).measurable,?_⟩,fun V=> hF V [] (by simp) (by simp)⟩
    unfold X tribute; positivity
lemma fertileD (x:Tick c): fertile x↔fertile (flopT x):=⟨And.symm,And.symm⟩
noncomputable def faceQ (A:BankP c) (C:ℝ) (a:ℝ)(B R n :ℕ)(d:Tick c):ℝ:=if fertile d then C*a^2*(silos A d+silos A (flopT d))*tribute B R n d.2.2 else 0
lemma forged (B R n N:ℕ): ∃ C:ℝ, 0 ≤ C ∧∀ (c:Side)(A:BankP c)(Γ:Silo c)(η δ a q:ℝ)(U:St c), Run.Pack id id η δ B U q Γ A →∀ p:BudgetPoint,p.order≤n→p.power≤R→p.threshold ≤ η→0<a→∀ d: Tick c,
     let V:=sealG Γ N; let L:= faceQ A C a B R n d; Woven (V.addr d).site (V.addr d).support p a (V.view d) L∧∀ U, Sen (V.addr d).site a (V.view d U)≤ L:=by
    obtain ⟨C,hp,H⟩:=asset B R n N; refine ⟨C,hp,fun c A Γ η δ a q U h p hn hr hv ht d=>?_⟩; intro V L
    by_cases he: fertile d; swap; · have hk(x): (sealG Γ N).view d x=0:=by
                                       have ht:= p.threshold_pos.trans_le hv; change nozzle c N (gleam Γ x d) = _; unfold gleam pairQ; rw [debtless h d x he ht,debtless h _ x (mt (fertileD _).2 he) ht,show ∀ i j:Site c, Stew.block i j (0:Bundle)=0 from fun i j=>map_zero (blockL i j),show Stew.block _ _ _=0 from map_zero (blockL _ _),add_zero,smul_zero,map_zero] -- syntax
                                    rw [show V.view d=0 from funext hk,show L=0 from if_neg he]; refine ⟨?_,fun W=>by rw [Pi.zero_apply,←measures,map_zero,norm_zero]⟩; simpa only [sum_empty] using Woven.sumX (o:=(V.addr d).site) (B:=(V.addr d).support) (p:=p) (a:=a) (fun i:Unit=>V.view d) ∅ (fun _=>0) (by simp) -- edit layout
    let E:= flopT d; have he':= (fertileD d).1 he; have hh:=H _ _ _ η δ _ _ _ h p hn hr hv ht d he _ he.1; have hg:= H _ _ _ η δ _ _ _ h p hn hr hv ht E he' _ he.1; let K:=tribute B R n d.2.2; let f(x:Tick c)(U:Grid c):= paleF N (pairQ Γ x U); have hx: V.view d=((2:ℝ)⁻¹) • (f d + f E):=by funext i; exact ( (nozzle c N).restrictScalars ℝ).map_smul _ _ |>.trans (congr_arg ((2:ℝ)⁻¹ • ·) ((nozzle c N).map_add ..))
    have hJ : L=(C*a^2 *silos A d)*K+(C*a^2*silos A E)*K:=by unfold L faceQ; rw [if_pos he,mul_add,add_mul]; 
    have h: (V.addr d).support=d.2.2:= if_pos he
    have hA:0 ≤ L:=hJ.symm ▸ (add_nonneg hh.1.travel hg.1.travel); have hc: ‖(2:ℝ)⁻¹‖*L ≤ L:=mul_le_of_le_one_left hA (by norm_num)
    rw [hx,h]; refine ⟨((hh.1.addition hg.1).byScalar ((2:ℝ)⁻¹)).stretches (Subset.refl _) (show ‖(2:ℝ)⁻¹‖*(C*a^2*silos A d*K+C*a^2*silos A E*K)≤ _ from hJ ▸ hc),fun U=>?_⟩
    rw [← measures]; let V:= (f d+f E) U; let p:= needle d.1 N a; change ‖p ((2:ℝ)⁻¹ • V)‖≤ L; rw [show p ((2:ℝ)⁻¹ • V)=_ from map_smul (p.restrictScalars ℝ) ((2:ℝ)⁻¹) V, norm_smul]; apply le_trans _ hc; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); unfold V; change ‖p (f d U+f E U)‖≤ _; rw [map_add]; exact (norm_add_le ..).trans ((add_le_add (hh.2 U) (hg.2 U)).trans_eq hJ.symm)
end YM.QCD.Entr
