import YM.Gust.TopP
import Mathlib.Analysis.Calculus.ContDiff.Bounds
set_option autoImplicit false
set_option maxHeartbeats 580000
noncomputable section
namespace YM.Massive.Gust
open Function Set Filter MeasureTheory Analysis Tarn Tarn.Choir Tarn.Choir.Strip UV Mater Kind Gala
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius ComplexOrder Matrix Classical
variable {K: Choir}{C:Sequence}{P:Calibration C}{T:Pollens P K}(hK:K.Domestic)(hf:Foil P K T){m n:ℕ}{x:Points m}(hx:x∈conf m)
local notation "Pz"=> Factory T n
local notation "W"=> Fin m → Stake T n
-- Unit inspection.Packed. Note universe.Oper.
lemma virtue (u: Fin m→ Stake T n)(x: Points (m+1))(hx:x∈conf _): valuation T n (m+1) x (Fin.cons (plant (relic hf n)) u)=valuation T n m (Points.tail x) u:=by
       let A:=valuation T n (m+1) x; let g:=valuation T n m (Points.tail x); let F:= A.curryLeft (plant (relic hf n)); refine recurs (fun r=> F r=g r) (fun q i h=> Eq.trans (F.map_coord_zero i h) (g.map_coord_zero i h).symm) (fun q=>?_) (fun q i x y h k=>by rw[F.map_update_add,g.map_update_add,h,k]) (fun q i x h c=>by rw[F.map_update_smul,g.map_update_smul,h]) u
       unfold F A g; rw[MultilinearMap.curryLeft_apply]; let S:= Fin.cons (α:=fun _=> Mater T n) (relic hf n) q; rw[show Fin.cons _ _=(fun i=> plant (S i)) from ?_,values,values]; swap; · ext1 i; cases i using Fin.cases<;> simp[S]
       unfold ValueP; rw[List.ofFn_succ]; change lead none _* _*_= _; simp_rw [loan_nil, one_mul]; refine congr_arg _ (Finset.prod_congr rfl fun i _=>?_); let R:=fun j:Fin m=> (q j).v i; have hx':(fun j=> (S j).v i)= Fin.cons (lampU P K) R:=by ext1 j; cases j using Fin.cases <;>rfl
       rw[hx']; exact hf.functor _ _ hx _ -- syntax?
variable (n)
lemma lawsB : (polarM hK hf n).Basic where
     trivial u x:=by rw[starts]; refine Eq.trans (congr_arg _ (show stint hK hf ∘ u=fun _=>plant (relic hf n) from Subsingleton.elim ..)) ?_; rw[values]; unfold ValueP; simp only[List.ofFn_zero,led,one_mul]; apply Finset.prod_eq_one; intro i _; rw[Subsingleton.elim x 0, show (fun _ : Fin 0=> (relic hf n).v i)=0 from Subsingleton.elim ..]; exact hf.empty
     unital h d v:=by rw[starts,starts,Fin.comp_cons]; rw [show stint hK hf ((Pz).one d)=plant (relic hf n) from laurel hK hf _]; exact virtue hf _ _ h
     same r _ h v:= movedB hf h (stint hK hf∘ v) r
lemma passes : (polarM hK hf n).Homogeneous:=fun m x h z v=> acrossP hf h _ z
lemma spinB : (polarM hK hf n).RealSpin where
     mirror s _ h v:=by
           rw [starts,starts]; let p:= chosenP s; have hv: ∀ i, Fees (stint hK hf ((Factory T n).move s (v i))) ((axisK hK (fromP s) T n) (stint hK hf (v i))):= fun i=> spinning hK hf _ s _ _; exact (face_any _ _ _ hv).trans ((show (chosenP s).coord=_ from fromP s) ▸ climbs hK hf h (stint hK hf ∘ v) (fromP s))
     real h v:= by rw[starts,starts]; have hu:∀ i, Fees (stint hK hf ((Factory T n).conjugate (v i))) (barK hK timeAxis T n (stint hK hf (v i))):=fun i=> walnut hK hf _ _; exact (face_any _ _ _ hu).trans (conj_poses hK hf h (stint hK hf ∘ v) timeAxis)
variable {n}
abbrev Cp (t:Points m→ℂ):Prop:=ContDiffOn ℝ ∞ t (conf m) ∧∀ j:ℕ, ∃ A : ℕ, ∃ C : ℝ, 0 ≤ C ∧∀ r : ℝ, 0 < r → r ≤ 1 → ∀ x : Points m, spaced r x → ‖iteratedFDeriv ℝ j t x‖ ≤ C * r⁻¹ ^ A
variable {u v:Points m→ℂ}(hu:Cp u)(hv:Cp v)
open Finset
lemma scareC(c:ℂ):Cp (fun _ : Points m=>c):=by
       refine ⟨contDiffOn_const,fun j=> ⟨0,‖c‖,norm_nonneg _,fun r hr _ x _=>?_⟩⟩; cases j <;> simp [iteratedFDeriv_succ_const,norm_nonneg]
include hu hv
lemma countsMul : Cp (fun y=>u y * v y) :=by
       refine ⟨hu.1.mul hv.1,fun j=> ?_⟩; choose d c h ha using hu.2; choose d' c' h' hb using hv.2; let a:= Finset.range (j+1); let D:= a.sup fun t=> d t + d' (j-t); let f(t:ℕ):ℝ:=(j.choose t:ℝ)*c t*c' (j-t)
       refine ⟨D, ∑ t∈a,f t,sum_nonneg (fun i _=>by unfold f; exact mul_nonneg (mul_nonneg (by positivity) (h i)) (h' _)),fun r hr H x hX=>?_⟩
       haveI:ContinuousSMul ℝ (Points m):= IsBoundedSMul.continuousSMul; have hZ:=spaced_conf hr hX; have ht:= norm_iteratedFDerivWithin_mul_le hu.1 hv.1 ((conf_open _).uniqueDiffOn) hZ (n:=j) (N:=∞) (by exact_mod_cast (show (j:ENat) ≤ ⊤ from le_top))
       simp_rw [iteratedFDerivWithin_of_isOpen _ (conf_open _) hZ] at ht
       refine ht.trans ?_; rw [Finset.sum_mul]; apply sum_le_sum; intro i hi
       refine le_trans (mul_le_mul (mul_le_mul_of_nonneg_left (ha i r hr H x hX) (by positivity)) (hb _ r hr H x hX) (norm_nonneg _) (mul_nonneg (by positivity) (mul_nonneg (h i) (by positivity)))) ?_
       calc _= f i*r⁻¹^(d i+d' (j-i)) := by rw [pow_add]; unfold f; ring
            _ ≤ f i*r⁻¹^D:= mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ((one_le_inv₀ hr).mpr H) (Finset.le_sup (s:=a) (f:=fun t=>d t+d' (j-t)) hi)) (mul_nonneg (mul_nonneg (by positivity) (h i)) (h' _))
lemma countsAdd : Cp (fun y=> u y + v y) :=by
       refine ⟨hu.1.add hv.1,fun j=>?_⟩; obtain ⟨a,c,hc,h⟩:=hu.2 j; obtain ⟨d,e,hE,H⟩:=hv.2 j
       refine ⟨max a d,c+e,add_nonneg hc hE,fun r hr hl x hx=>?_⟩; have hs:=spaced_conf hr hx
       haveI:ContinuousSMul ℝ (Points m):= IsBoundedSMul.continuousSMul; rw [show (fun x=>u x+v x)=u+v from rfl,iteratedFDeriv_add_apply ?_ ?_,add_mul]; · exact (norm_add_le ..).trans (add_le_add ((h _ hr hl _ hx).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ((one_le_inv₀ hr).mpr hl) (le_max_left ..)) hc)) ((H _ hr hl _ hx).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ((one_le_inv₀ hr).mpr hl) (le_max_right ..)) hE)))
       · exact ((hu.1.of_le (show (j:ℕ∞ω)≤ ∞ from by exact_mod_cast (show (j:ENat) ≤ ⊤ from le_top))).contDiffAt ((conf_open _).mem_nhds hs))
       exact (hv.1.of_le (show (j:ℕ∞ω)≤ ∞ from by exact_mod_cast (show (j:ENat) ≤ ⊤ from le_top))).contDiffAt ((conf_open _).mem_nhds hs)
omit hu hv
include hK
lemma coupons (v:Fin m→Stake T n): Cp (fun x=> valuation T n m x v) :=by
       let X(s: Fin m→Stake T n):= Cp (fun x=>valuation T n m x s); refine recurs X (fun r i h=>?_) (fun i=>?_) (fun a i x y h k=>?_) (fun p i x h c=>?_) _
       · unfold X; simp_rw [MultilinearMap.map_coord_zero _ _ h]; exact scareC 0
       · let Crx(j:Fin (n+1))(x:Points m):= K.total m x (fun r=> (i r).v j); have hh(s:Finset (Fin (n+1))): Cp (fun x: Points m=>∏ j∈s,Crx j x):=by
            induction s using Finset.induction_on with
            | empty=> simpa only [Finset.prod_empty] using scareC (m:=m) 1
            | @insert j s hi h=>simp_rw[Finset.prod_insert hi]; exact countsMul (show Cp (Crx j) from ⟨hK.smooth m _,hK.thick m _⟩) h
         unfold X; simp_rw[values,ValueP]; exact countsMul (scareC _) (hh univ)
       · unfold X; simp_rw [MultilinearMap.map_update_add]; exact countsAdd h k
       · unfold X; simp_rw [MultilinearMap.map_update_smul]; exact countsMul (scareC _) h
include hf
variable (n)
lemma smoothP : (polarM hK hf n).Smooth:=⟨fun _ v=> (coupons hK (fun i=> launch hK hf n _ (v i))).1⟩
lemma costs : (polarM hK hf n).Capped:=fun m d v j=> (coupons hK (fun i=> launch hK hf n _ (v i))).2 j
end YM.Massive.Gust
#print axioms YM.Massive.Gust.lawsB
#print axioms YM.Massive.Gust.costs
