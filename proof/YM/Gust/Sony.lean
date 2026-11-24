import YM.Gust.Pitch
import YM.Gust.Sum
set_option autoImplicit false
set_option maxHeartbeats 670000
noncomputable section
namespace YM.Massive.Gust
open Function Set Filter MeasureTheory Analysis Tarn Tarn.Choir Tarn.Choir.Strip UV Mater Kind Gala QCD QCD.Lat
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius ComplexOrder Matrix InnerProductSpace Classical
variable {K: Choir}{C:Sequence}{P:Calibration C}{T:Pollens P K}(hK:K.Domestic)(hf: Foil P K T){m n k d:ℕ}{x:Points (m+1)}(hx:x∈conf _)
local notation "F"=> Factory T n
local notation "S"=> polarM hK hf n
local notation "Hq"=> Clouds hK hf n
local notation "ξ"=> launch hK hf n
open Tarn.ChargeQ Patria Patria.Gall Onyx
variable (A:Axis×Axis→K.W) (hA:Persona T A) (V:Axis×Axis→(Factory T n).Ref 4)(hV:∀ i:Axis×Axis, Fees (launch hK hf n 4 (V i)) (plant (markR hf A hA i.1 i.2 n)))
local notation "L" i:arg j:arg=> A (i,j)
local notation "R" i:arg j:arg=>markR hf A hA i j n
set_option quotPrecheck false
local notation "Θ" i:arg j:arg=>(S).project 4 (V (i,j))
open Finset
variable (a b:Axis)
-- only use HQ.Domestic need continuity arc lamp.Direct.
include hf hK in
lemma ring0: K.arc a (lampU P K)=0:=by
      apply detected hf; intro n p x hx
      have he: (fun t=> K.total _ (Ward.cast x 0 a t) (Fin.cons (lampU P K) p)) =ᶠ[𝓝 0] fun _=>K.total _ (Points.tail x) p:=by
            obtain ⟨χ,hχ⟩:= Work.A01.exists_window x hx; filter_upwards [Work.A02.stable hx hχ a] with t ht; rw[hf.functor _ _ ht.1, show Points.tail (Ward.cast x 0 a t) = _ from ?_]; refine PiLp.ext (fun i=>?_); exact Ward.near _ _ _ i.succ_ne_zero _ t -- args
      rw[heads, map_zero (headG ..)]; exact (he.hasDerivAt_iff.mp (Gust.deriv_head hK hx a (lampU P K) p)).unique (hasDerivAt_const ..)
include hA in
lemma soma : ∑ i:Axis,K.arc i (L i b)=0:= by
       have h:=congr_fun hA.div b; unfold divR at h; rw[LinearMap.pi_apply,LinearMap.sum_apply] at h; exact h
include hf hK hA
lemma leaps_zero : Fees (∑ i:Axis,leaps hK hf i n (plant (markR hf A hA i b n))) 0 :=by
       intro M; simp_rw [map_zero,map_sum]; unfold leaps; simp only [plant,Finsupp.linearCombination_single,one_smul]; rw [← map_sum, sum_comm]; rw [map_sum]; apply sum_eq_zero; intro j _; rw [map_sum]; induction j using Fin.cases with
       | zero=>
              let f :=fun _i:Fin n=> lampU P K; have ht(a:Axis): (roamF hK hf a 0 (R a b)).v= Fin.cons (K.arc a (L a b)) f:=by
                    funext i; cases i using Fin.cases <;> first| rfl| (simp[markR,passP,roamF,f])
              let V:= (M none); change ∑ a:Axis,_= _; change ∑ a:Axis, morph M (plant (roamF _ _ a 0 (R a b)))=0; simp_rw[once]; -- linear slot M at revised head
              change ∑ a:Axis, V _=0; simp_rw [ht,← MultilinearMap.curryLeft_apply]; rw [← MultilinearMap.sum_apply,← map_sum,soma A hA b,map_zero]; rfl -- wrong: curryLeft Σ v gives multilinear. use `←MultilinearMap.sum_apply`
       | succ i=> refine sum_eq_zero fun a _=> ?_; rw [show morph M (Finsupp.single _ _) = _ from once ..]; refine MultilinearMap.map_coord_zero _ i.succ ?_; change update _ _ _ _=_; rw [update_self]; exact ring0 hK hf a
omit hf hK hA
-- clean discrepancy jumps. enough Q.M.
variable (D :Spiral.DiffPlan (polarM hK hf n))(hd : D.Derivatives (polarM hK hf n))
variable (p:Fin m→(Factory T n).Token)
include hf hK hA hd hx hV
lemma axisHead : (S).useAt S x (Fin.cons (⟨4+1, D.deriv 4 a (Θ a b)⟩:(S).Tag) ((S).classTokens ∘p))= valuation T n _ x (Fin.cons (leaps hK hf a n (plant (R a b))) (stint hK hf ∘p)):=by
       rw[hd.kernels _ _ _ hx]; let Fz(y:Points (m+1)) := (S).useAt S y (Fin.cons ⟨4,Θ a b⟩ ((S).classTokens∘ p)); let Rz(y:Points (m+1)):= valuation T n _ y (Fin.cons (plant (R a b)) (stint hK hf∘p)); have hU(y:Points (m+1))(hx:y∈conf (m+1)): Fz y=Rz y:=by
             unfold Fz; rw [zoomT _ _ p _ _ hx]; unfold yawn; rw [starts, Fin.comp_cons]; exact fosters _ _ _ (hV (a,b)) _
       have hZ:= Gust.greatness_single hK hf hx a (R a b) (stint hK hf ∘ p)
       have hDif:DifferentiableAt ℝ Fz x := (((S).class_smooth S (Hq).smooth _).contDiffAt ((conf_open _).mem_nhds hx)).differentiableAt (by simp)
       let f:= Ward.cast x 0 a; have h:= Ward.moves x 0 a 0; rw[← Ward.start x 0 a] at hDif -- recursive affects? rw x occurrences in Fz? binder Fz independent.
       haveI:ContinuousSMul ℝ (Points (m+1)):= IsBoundedSMul.continuousSMul
       have ht:=hDif.hasFDerivAt.comp_hasDerivAt 0 h; rw [Ward.start] at ht; refine ht.unique ?_; refine (show Fz ∘ f=ᶠ[𝓝 0] Rz ∘ f from ?_).hasDerivAt_iff.mpr hZ -- function need F comp
       obtain ⟨χ,hχ⟩:= Work.A01.exists_window x hx; exact (Work.A02.stable hx hχ a).mono fun t ht=> hU (f t) ht.1
omit hx
--
lemma warrant : ∑ i:Axis,D.deriv 4 i (Θ i b)=0:=by
       apply (S).faithfully; funext x; obtain ⟨m,x,v,hx⟩:=x; rw [map_sum,Finset.sum_apply, map_zero]; change ∑ i:Axis,_=0; simp_rw [← (S).through (Hq).laws.toSymmetric _ v hx, axisHead hK hf hx A hA V hV _ b D hd v] -- args
       let p:= stint hK hf ∘v; let Pz:= valuation T n (m+1) x; change (∑ i:Axis,Pz.curryLeft _ p)=_
       rw [← MultilinearMap.sum_apply, ← map_sum]; change valuation T n _ x _=_; refine Eq.trans (fosters p _ 0 (leaps_zero hK hf A hA b) x) (Pz.map_coord_zero (0:Fin (m+1)) rfl)
lemma dressC : Spiral.Table.Conserved D (Hq).spin (fun i j=>Θ i j):=⟨symL hK hf A hA V hV,roseK hK hf A hA V hV,fun i=> warrant hK hf A hA V hV i D hd⟩
omit hd
lemma orientedSS : Spiral.Table.RawTensor (Hq).spin (fun i j=>Θ i j):=by
       intro k a b; rw[movedSS hK hf A hA V hV]
       symm; rw [sum_eq_single (k.perm a)]
       · rw [sum_eq_single (k.perm b)]; · rw [Signed.matrix_at,Signed.matrix_at]; simp only [↓reduceIte]; rfl
         · intro i _ hh; simp [Signed.matrix_at,Ne.symm hh]
         simp
       · intro i _ hh; simp [Signed.matrix_at,Ne.symm hh]
       simp
end YM.Massive.Gust
#print axioms YM.Massive.Gust.dressC
#print axioms YM.Massive.Gust.orientedSS
