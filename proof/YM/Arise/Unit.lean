import YM.Arise.Pair
import YM.Bank.Pic
import YM.Arise.Labels
import YM.Next.RANK.GaussLeg
/-! # Sway curls. -/
set_option autoImplicit false
noncomputable section
namespace YM.Arise.Range
open Function Lattice Finset Wilson Filter MeasureTheory Tensor Work.G06 RG
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical TensorProduct
open Labels Maxwell Analysis
variable {r n m i j k d e:ℕ}
variable {G: Gauge}(p: Axis)(x y: E4)
variable {z:E4}
variable {F M:Type}[NormedAddCommGroup F][NormedSpace ℝ F][NormedAddCommGroup M][NormedSpace ℝ M]
local notation "ear"=> Bank.Kith.earn
noncomputable def deriveL (a:List Axis)(f:E4→F):=a.foldr (fun i g=> Analysis.D (basis i) g) f
lemma balla (a:List Axis)(f:E4→F)(U:Set E4)(hU:IsOpen U)(h:∀ z∈U,ContDiffAt ℝ ∞ f z) : ∀ x∈U, ContDiffAt ℝ ∞ (deriveL a f) x:=by
    induction a with|nil=>exact h|cons i l ih=> exact fun x hx=> (Analysis.dSmooth (ih x hx) _ (m:=∞) (by simp) : _)
lemma lyras (a b: List Axis)(f:E4→F): deriveL (a++b) f=deriveL a (deriveL b f):=by simp [deriveL,List.foldr_append]
lemma probeL (a:List Axis)(f:E4→F){U:Set E4}(hU: IsOpen U)(hp:∀ x∈ U, ContDiffAt ℝ ∞ f x): ∀ x∈U, deriveL a f x= a.length.factorial • Tensor.coeff f a.length x (basis∘a.get):=by
    have h1 : ∀ x∈U,deriveL a f x= iteratedFDeriv ℝ a.length f x (basis∘a.get):=by induction a with
       | nil=>intro x hx; rw [show iteratedFDeriv ℝ ([]:List Axis).length f x (basis ∘[].get)=f x from ?_]; rfl
              exact iteratedFDeriv_zero_apply ..
       | cons i a ih=>
          intro x hx; rw [show basis ∘ (i::a).get=Fin.cons (basis i) (basis∘a.get) from ?_]; change _ = iteratedFDeriv ℝ (a.length+1) _ _ _; rw [cons_jet]; -- hf syntax
          · exact GermD _ (Filter.Eventually.mono (show ∀ᶠ y in 𝓝 _,y∈ U from hU.mem_nhds hx) fun y hy => ih y hy)
          · exact (hp x hx).of_le (WithTop.coe_le_coe.mpr le_top)
          funext v; refine Fin.cases ?_ (fun i=>?_) v <;> simp
    intro x hx; rw [h1 x hx,Tensor.coeff,← Nat.cast_smul_eq_nsmul ℝ, smul_apply]; rw [smul_smul,mul_inv_cancel₀ (by positivity),one_smul]
lemma commute_a {U:Set E4}(hU:IsOpen U)(f:E4→F)(hp:∀ x∈ U,ContDiffAt ℝ ∞ f x)(l l':List Axis)(h:l.Perm l'): ∀ x∈U, deriveL l f x=deriveL l' f x:=by
    induction h with
    | nil=>simp
    | cons a h ih=>exact fun x hx=> GermD _ (Filter.Eventually.mono (show ∀ᶠ y in 𝓝 _,y∈ U from hU.mem_nhds hx) fun y hy=>ih y hy)
    | swap i j l=> intro x hx; exact commuteD ((balla l f U hU hp x hx).of_le (show (↑(2:ℕ):WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)) ..
    | trans h v ih ig=> exact fun x hx=>(ih x hx).trans (ig x hx)
lemma spiral {U:Set E4}(hU:IsOpen U)(f:E4→F)(hp:∀ x∈ U,ContDiffAt ℝ ∞ f x)(l:List Axis)(L:F→L[ℝ] M): ∀ x∈U, deriveL l (L ∘ f) x=L (deriveL l f x):=by
     induction l with|nil=>exact fun _ _=> rfl|cons a l ih=>intro x hx; refine Eq.trans ((GermD (f:=deriveL l (L ∘ f)) (g:=L ∘deriveL l f) (basis a) (Filter.Eventually.mono (show ∀ᶠ y in 𝓝 _,y∈ U from hU.mem_nhds hx) (fun y hy=>ih y hy)))) (grad_linear L (balla l f U hU hp x hx) _)
section Therm
open Massive Massive.UV UV.Free QCD QCD.Lat
lemma is_hot (a b: Pinor): ∀ x∈away,ContDiffAt ℝ ∞ (dirac a b) x:=by
    intro x hx; change ContDiffAt ℝ ∞ (fun x => -(∑ i, gamma i a b * ((D (basis i) Green x:ℝ):ℂ))) x; exact (ContDiffAt.sum (fun i _=> ContDiffAt.mul contDiffAt_const (Complex.ofRealCLM.contDiff.contDiffAt.comp (f:=grad i Green) x (gradGradientSmooth hx i)))).neg -- expression minus? check unary
lemma zero_strike(l: List Axis): deriveL l (0:E4→ℂ)=0:=by induction l with|nil=>rfl|cons a l ih=>rw [show deriveL (a::l) _=Analysis.D (basis a) (deriveL l (0:E4→ℂ)) from rfl,ih]; ext x; all_goals simp [Analysis.D]
lemma tours (i: SpinMode d)(j: SpinMode e)(h:x≠ y): leg i j x y= if i.2=j.2 then YM.Bank.Pic.stove (YM.Bank.Ivo.s_k i.1.2 j.1.2) (steps i.1.1) (steps j.1.1) (x-y) else 0 :=by
    let a:=i.1.1; let b:=j.1.1; let p:=i.1.2; let q:=j.1.2; unfold leg; by_cases ht:i.2=j.2; swap; · simp [ht]
    rw [if_pos ht]; unfold YM.Bank.Pic.stove; by_cases hf:p.2=q.2
    · rw [if_pos ⟨hf,ht⟩,show YM.Bank.Ivo.s_k p q=dirac p.1 q.1 from funext fun i=> if_pos hf]; change (-1:ℂ)^(steps b).length * deriveL (steps a++steps b) (dirac p.1 q.1) (x-y)=(-1:ℂ)^_*deriveL (steps b) (deriveL _ _) _; rw [← lyras]; apply congr_arg; exact commute_a open_away _ (is_hot _ _) _ _ (List.perm_append_comm ..) (x-y) (sub_ne_zero.mpr h)
    rw [if_neg (fun hy=>hf hy.1), show YM.Bank.Ivo.s_k p q=0 from funext fun i=>if_neg hf]; change 0=(-1:ℂ)^_* deriveL (steps _) (deriveL _ (0:E4→ℂ)) _; rw [zero_strike,zero_strike]; exact (mul_zero _).symm
end Therm
section Coil
-- off-shell stencil probe with its correct natural factor
local notation "R"=> G.ColorIndex
noncomputable def dollar (k:ℕ)(a:Proto k)(i:G.ColorIndex): Probe G k:= constrain ((k.factorial:ℝ) • Maxwell.fromF G (basis∘a.2) i a.1.val.1 a.1.val.2)
lemma gaugeWet(p:PlaqAxes)(i:G.ColorIndex)(l:List Axis)(s:PlaqAxes)(j:G.ColorIndex)(r:List Axis)(h:x≠y): (legKernel (dollar l.length (p,l.get) i) (dollar r.length (s,r.get) j) (x-y):ℂ)=if i=j then YM.Bank.Pic.stove (YM.Bank.Ivo.from_p p s) l r (x-y) else 0:=by
     let f:=bareCurl p.val.1 p.val.2 s.val.1 s.val.2; let a:=l.length; let b:=r.length; let v:= basis ∘ l.get; let u:=basis ∘ r.get
     have ht:∀ x∈away, ContDiffAt ℝ ∞ f x:=fun x hx=>Bare.curl_diff hx _ _ _ _
     have he :∀ x∈away,ContDiffAt ℝ ∞ (deriveL l f) x:=balla l f away open_away ht; have hx:x-y≠0:=sub_ne_zero.mpr h
     change (↑(pairing (show (x-y)∈away from hx) _ _):ℂ)=_
     rw [show dollar a _ i=(↑(Nat.factorial a):ℝ) • constrain (G:=G) (Maxwell.fromF G v i p.val.1 p.val.2) from rfl,show dollar b _ j=(↑(Nat.factorial b):ℝ) • constrain (G:=G) (Maxwell.fromF G u j s.val.1 s.val.2) from rfl]; rw [map_smul,map_smul,LinearMap.smul_apply, raw_mixed v u _ _ _ _ _ _ hx]; by_cases hp:i=j; swap; · simp [hp]
     rw [if_pos hp,if_pos hp]; let L:=Complex.ofRealCLM; change _= (-1:ℂ)^b * deriveL r (deriveL l (L∘f)) (x-y); rw [← lyras, spiral open_away f ht _ L (x-y) hx, lyras]
     have hu: deriveL l f =ᶠ[𝓝 (x-y)] fun z=> (a.factorial:ℝ) • coeff f a z v:= Filter.Eventually.mono (show ∀ᶠ w in 𝓝 _, w∈away from open_away.mem_nhds hx) (fun _ hc=>(probeL l f open_away ht _ hc).trans (Nat.cast_smul_eq_nsmul ℝ ..).symm)
     have hQ: ContDiffAt ℝ (r.length:WithTop ℕ∞) (fun z=>coeff f a z v) (x-y) := ((ContinuousMultilinearMap.apply ℝ _ _ v).contDiff.contDiffAt.comp _ (Tensor.coeff_smooth (ht _ hx) a)).of_le (WithTop.coe_le_coe.mpr le_top)
     rw [probeL r (deriveL l f) open_away he (x-y) hx,Tensor.GermCoeff b hu]; rw [show (fun z=> (a.factorial:ℝ) • Tensor.coeff f a z v)=(a.factorial:ℝ) • (fun z=>Tensor.coeff f a z v) from rfl,Tensor.coeff_smul _ hQ]; change ↑((↑b.factorial:ℝ)*(↑a.factorial *((-1)^b * _))) = (-1:ℂ)^b * (↑(_ :ℝ):ℂ); rw [smul_apply]; simp [Nat.cast_smul_eq_nsmul]; push_cast; ring
end Coil
end YM.Arise.Range
#print axioms YM.Arise.Range.tours
#print axioms YM.Arise.Range.gaugeWet
