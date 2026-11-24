import YM.Pollen.Hops
import YM.Helio.Gate
import YM.Massive.PCAC.Bare
set_option autoImplicit false
noncomputable section
namespace YM.Massive.PCAC
open QCD QCD.Lat Function Lattice Wilson Creek Grass Ledge Lat Finset NormedSpace RG Cove Cove.Send Filter Run
open MeasureTheory QCD.Grass.Ward
open scoped Topology BigOperators ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{k N:ℕ}{t a b:ℝ}{o: Site c} {P:BudgetPoint}
open Further.DenseMixedKernels
local notation "M"=> Modes c N
local notation "Q"=>Sour M
set_option quotPrecheck false
local notation "ν" V:arg W:arg=> fun X:Grid c=>(applyMark false (V X) - applyMark true (W X)).toContinuousLinearMap
variable (x y:Grid c→ Sour (Modes c N))
open scoped Kronecker
open Kit Sway Stew
variable (p:Site c)(a:Axis)(X:Spike)(f:Flavor N)
-- primitive current.Pl.k. Sign from body orientation.PC.Sp.Gamma chosen
noncomputable def keel (V:Grid c): Sour (Modes c N):= zone N p * (Stew.delta V a ⊗ₖ spot f f)
noncomputable def keelB (V:Grid c):Sour (Modes c N):= (Stew.delta V a ⊗ₖ spot f f)*zone N p
local notation "V'"=>keel p a f
local notation "T'"=>keelB p a f
noncomputable def mixΛ := ν x y
local notation "F'"=> mixΛ V' T'
lemma starspot (f:Flavor N): star (spot f f)=spot f f:=by ext i j; unfold spot; change star (if _ then _ else _)=_; simp_rw [apply_ite star]; simp [and_comm]
lemma starKeel : T' = fun i=> -star (V' i):=by
   funext i; unfold keelB keel; rw[star_mul,Lat.star_kr,δ_back,starspot,zstar]; ext i j; simp only [Matrix.neg_apply,Matrix.mul_apply, Matrix.kronecker_apply]; simp -- push neg
variable (c N) -- wrong `N` Nat? inferred from section binder Order? keyword
lemma chin (n b:ℕ): ∃ C:ℝ,0 ≤ C∧ ∀ (c:Side)(P:BudgetPoint),P.order≤ n→ P.power ≤ b→∀ (a:Axis)(p:Site c)(f:Flavor N), Fetch p false (keel p a f) P C ∧ Fetch p true (keelB p a f) P C:=by
     obtain ⟨C,hc,H⟩:= Stew.prices n b 1; let E:= voucher N (‖TouchL‖*C); let ζ:=(2:ℂ)⁻¹; have hE:0 ≤ E:=(by unfold E voucher; positivity); refine ⟨‖ζ‖*E+‖-ζ‖*E,add_nonneg (mul_nonneg (norm_nonneg _) hE) (mul_nonneg (norm_nonneg _) hE),fun c P hh ht a p f=>?_⟩
     have hp (i:Step):Fetch p false (gateH p i f) P E:=shaft p i f _ (zero_le_one.trans hc) (fun e he=> H c p e he P hh ht); let X:= gateH p (posDir a) f; let Y:= gateH p (negDir a) f; have hp :=plusP _ _ false (scaleP _ ζ false (hp (posDir a))) (scaleP _ (-ζ) false (hp (negDir a)))
     have hk: ζ • X + -ζ • Y=keel p a f:=by
          funext V; unfold X Y keel Stew.delta; ext i j; simp only [gateH,zleft,Matrix.kronecker_apply, neg_smul, Pi.add_apply,Pi.smul_apply,Pi.neg_apply,Matrix.add_apply,Matrix.smul_apply,Matrix.neg_apply,Matrix.sub_apply, smul_eq_mul]; split<;> simp [posDir,negDir, Kit.leg, ζ] <;> ring -- expensive
     rw [show ζ • X + _= _ from hk] at hp -- left side defin? sign syntax
     exact ⟨hp,by rw [starKeel]; exact flowback _ hp⟩
variable {c N}
local notation "X*"=>fun (_:Grid c)=> localF p X f f
lemma poleBoth (P:BudgetPoint)(v:Bool):Fetch p v (X*) P (veinFare X):=by
      let V:=localF p X f f; have hh(k: Frame c):Commute (Lat.rotates N k) V:= (commute_zone p k|>.symm).mul_right (commuteSpin f f X k); refine ⟨fun _ _ _=>rfl, fun i j U ht=>?_,fun _ j=>by
          change V=(rotates N j)*V*star (rotates N j); rw [show (rotates N j)*V=V*_ from (hh j).eq,mul_assoc,(rotates_law ..).2,mul_one], sum_nonneg fun i _=>sum_nonneg fun j _=> norm_nonneg _, ?_⟩ -- edit
      · have he:i.1.1=p:= by_contra fun he=>ht (focusL _ _ p X i j he); have hr:j.1.1=p:=by_contra fun he=> ht (focusR _ _ p X i j he); have hu:p∈ halo 1 {p}:=halo_subset _ _ (mem_singleton_self _); split; exact ⟨hr,he.symm ▸ hu⟩; exact ⟨he,hr.symm ▸hu⟩
      exact ⟨fun i j=>‖V i j‖,(veinSum f f p X).le,fun i j=>⟨norm_nonneg _,continuous_const,fun i' j'=> Pitch.fixed _ (by positivity)⟩⟩
lemma orbitKeel (C:ℝ)(h:Fetch p false V' P C)(he:Fetch p true T' P C) : Suit p P (C+C) F':=populate _ _ h he fun V=> Matrix.trace_mul_comm _ _
lemma orbitA : Suit p P (veinFare X+veinFare X) (mixΛ (X*) (X*)):=populate _ _ (poleBoth ..) (poleBoth ..) fun _=>rfl
end YM.Massive.PCAC
#print axioms YM.Massive.PCAC.chin
#print axioms YM.Massive.PCAC.orbitA
