import YM.QCD.Pearl.Shore

/-!
# 1st jet of D carries k→k+p; 2nd k invariant. ordinary complex perturbative plane
closure in the analytic determinant branch at zero.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Pearl
open Lattice Wilson Function Finset Metric Lat Rudder Kit NormedSpace RG
open Laurent Bloch Flume YM.Next.Free
open scoped Matrix Matrix.Norms.L2Operator BigOperators Topology ContDiff
variable {n : Side} (C : su.Color)
lemma spurs {m} (U : Bloom m):Differentiable ℂ (blossom C U (n:=n)):=differentiable_pi.mpr fun i=>petals_open C U i -- dotted placeholder eats
lemma leafZero {m : ℕ} (h:0<m)(W: Bloom m): (blossom (n:=n) C W 0)=0:= by
  funext x; unfold blossom; refine sum_eq_zero fun i _=>?_; rw [prod_eq_zero (mem_univ (⟨0,h⟩:Fin m)), zero_smul]; simp only [tick,bill0,bore_nil]
lemma tickD (i:su.ColorIndex)(S : Slot)(x : Site n):Differentiable ℂ (bore C i ∘ tick S x):= (bore_diff C i).comp (billD _ _)
lemma tick_dew (u : Weather n) (i : su.ColorIndex) (S : Slot) (x:Site n): dew u (bore C i ∘ tick S x) 0=tick S x u*(C i:ℂ):=by
  obtain ⟨L,h⟩:= shifts (wrap n S.offset+x) (Lattice.square S.plaq.val.1 S.plaq.val.2); have he:tick S x=L:= (funext h).symm
  rw [he,dew_chain L.differentiableAt (bore_diff C i _),dewp,map_zero,dew_ℂ,(bore_first C i).deriv]; rfl
lemma tick_dig (u v: Weather n) (i : su.ColorIndex) (S : Slot) (x:Site n):dig u v (bore C i ∘ tick S x) 0=0:=by
  obtain ⟨L,h⟩:= shifts (wrap n S.offset+x) (Lattice.square S.plaq.val.1 S.plaq.val.2); have he:tick S x=L:= (funext h).symm; rw [he,dig_plain (bore C i) L _ _ _ (bore_diff C i),map_zero,bore_dig]
lemma dew_tw {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] (g:E→ℂ)(h:Differentiable ℂ g)(u v:E)(Z:F):dew u (fun x=>g x • Z) v=dew u g v • Z:=by rw [dew_s (h v) (differentiableAt_const Z),dew_zero, smul_zero,zero_add]
lemma dig_tw {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] (g:E→ℂ) (h:Differentiable ℂ g)(u v x:E)(Z:F): dig u v (fun t=>g t • Z) x=dig u v g x • Z:=by unfold dig; rw [funext (fun x=>dew_tw g h v x Z),dew_tw]; intro x; exact voiced _ (PolyDisc.finiteD _ (Filter.Eventually.of_forall h))

def bloomC {m : ℕ}(W:Bloom m):Bundle:=∑ i,(∏ j,(C (i j):ℂ)) • W.coeff i
lemma moss₁ (u : Weather n) (W : Bloom 1) (x:Site n):dew u (fun z=> blossom C W z x) 0=tick (W.petals 0) x u • bloomC C W:=by
  let f (i:Fin 1→su.ColorIndex):=bore C (i (0:Fin 1)) ∘ tick (W.petals 0) x
  have hp i:Differentiable ℂ (f i):= tickD C _ _ _
  unfold blossom bloomC; simp_rw [Fin.prod_univ_one]
  rw [show (fun z=> ∑ i,bore C (i (0:Fin 1)) _ • W.coeff i)= (fun z=>∑ i,f i z • W.coeff i) from rfl]
  rw [jot univ (fun i z=> f i z • W.coeff i) (fun i _=> (hp i).smul_const _) u u 0,smul_sum]
  exact sum_congr rfl fun i _=> by rw [dew_tw _ (hp i)]; unfold f; rw [tick_dew,smul_smul]
lemma mud₁ (u v: Weather n)(W:Bloom 1)(x:Site n): dig u v (fun z=> blossom C W z x) 0=0:=by
  let f (i:Fin 1→su.ColorIndex):= bore C (i (0:Fin 1)) ∘ tick (W.petals 0) x
  unfold blossom; simp_rw [Fin.prod_univ_one]
  change dig u v (fun z=>∑ i,f i z • W.coeff i) 0=0
  rw [jip]; apply sum_eq_zero; intro i _; rw [dig_tw _ (tickD C _ _ _)]; rw [tick_dig,zero_smul]
  exact fun i _=> (tickD C _ _ x).smul_const _
def jewels (x:Site n) (W: Bloom 2)(u v:Weather n):= tick (W.petals 0) x u*tick (W.petals 1) x v+tick (W.petals 0) x v*tick (W.petals 1) x u
lemma moss₂ (u : Weather n) (W : Bloom 2) (x:Site n):dew u (fun z=> blossom C W z x) 0=0:=by
  let f (i:Fin 2→su.ColorIndex)(a:Fin 2):= bore C (i (a:Fin 2)) ∘ tick (W.petals a) x
  have hp i a : Differentiable ℂ (f i a):= tickD C _ _ _ -- check
  let g i z:=f i 0 z * f i 1 z
  unfold blossom; simp_rw [Fin.prod_univ_two]; change dew u (fun z=>∑ i,g i z • W.coeff i) 0=0
  rw [jot _ (fun i z=>g i z • W.coeff i) (fun i _=> ((hp i 0).mul (hp i 1)).smul_const _) u u]
  apply sum_eq_zero; intro i _; rw [dew_tw _ (show Differentiable ℂ (g i) from (hp i 0).mul (hp i 1))]; unfold g; rw [dew_mul (hp i 0 _) (hp i 1 _)] -- issue `g`
  simp only [f,Function.comp_apply,tick,bill0,bore_nil, mul_zero,zero_mul,add_zero,zero_smul]
lemma mud₂ (u v: Weather n)(W:Bloom 2)(x:Site n): dig u v (fun z=> blossom C W z x) 0=jewels x W u v • bloomC C W:=by
  let f (i:Fin 2→su.ColorIndex)(a:Fin 2):= bore C (i (a:Fin 2)) ∘ tick (W.petals a) x
  have hp i a : Differentiable ℂ (f i a):= tickD C _ _ _
  let g i z:=f i 0 z * f i 1 z
  unfold blossom bloomC; simp_rw [Fin.prod_univ_two]; change dig u v (fun z=> ∑ i, g i z • W.coeff i) 0=_
  rw [jip _ (fun i z=>g i z • W.coeff i) (fun i _=> ((hp i 0).mul (hp i 1)).smul_const _) u v,smul_sum]; refine sum_congr rfl fun i _=> ?_
  rw [dig_tw _ (show Differentiable ℂ (g i) from (hp i 0).mul (hp i 1))]; unfold g; rw [drip_prod (hp i 0) (hp i 1)]; simp only [f, tick_dew,dig,Function.comp_apply, tick,bill0,bore_nil, mul_zero,zero_mul,add_zero,zero_add,smul_smul]; unfold jewels; congr 1; dsimp only [tick]; ring
lemma low_silt {m : ℕ}(t:Site n)(W: Bloom m)(h:0<m): silt C t W 0=0:=by unfold silt; rw [leafZero C h W,(show rides (Equiv.refl (Site n)) (0:Site n→Bundle)=_ from ride_zero _), zero_mul]

def upL (u:Weather n)(W:Bloom 1):= rides (Equiv.refl _) (fun x=> tick (W.petals 0) x u • bloomC C W)
lemma silt_dew (U:Bloom 1)(t:Site n)(u:Weather n):dew u (silt C t U) 0=upL C u U * routeM t 1 U.tail:=by
  let f z:= gate n (blossom C U z); have hf : Differentiable ℂ f:= (gate n).differentiable.comp (spurs C _)
  change dew u (fun z=> f z * amass C t U.tail z) _ = _
  rw [dew_mul (hf _) (hooked C _ _ _),show f 0=0 from (by change rides _ _= _; rw [leafZero C (by decide) U]; exact ride_zero _), amass0,zero_mul,zero_add]; congr 1; change dew u (fun z=> rides (Equiv.refl _) (blossom C U z)) _=_; rw [drip_gate _ (spurs C _),upL]; congr 1; funext x; exact moss₁ ..
lemma silt₂ (U:Bloom 2)(t:Site n)(u:Weather n):dew u (silt C t U) 0=0:=by
  let f z:= gate n (blossom C U z); have hf : Differentiable ℂ f:= (gate n).differentiable.comp (spurs C _)
  change dew u (fun z=> f z * amass C t U.tail z) _ = _
  rw [dew_mul (hf _) (hooked C _ _ _),show f 0=0 from (by change rides _ _= _; rw [leafZero C (by decide) U]; exact ride_zero _),zero_mul]; change 0 + dew u (fun z=> rides (Equiv.refl _) (blossom C U z)) 0 * _ = _; rw [drip_gate _ (spurs C _),funext (moss₂ C u U),ride_zero,zero_mul,zero_add]
lemma hewn (t:Site n)(W:Bloom 1)(u v:Weather n):dig u v (silt C t W) 0=(upL C u W*pump v W.tail (touch (echo C))+upL C v W * pump u W.tail (touch (echo C)))*routeM t 1 W.tail:=by
  let f (z:Weather n):= rides (Equiv.refl _) (blossom C W z); have hf : Differentiable ℂ f:= (gate n).differentiable.comp (spurs C _)
  change dig u v (fun z=> f z*amass C t W.tail z) 0= _; rw [drip_prod hf (hooked C t _),show f 0=0 from (by unfold f; rw [leafZero C (by decide) W]; exact ride_zero _),zero_mul,amass_dew,amass_dew,zero_add]
  unfold f; rw [drip_gate _ (spurs C _),drip_gate _ (spurs C _),dive_gate _ (spurs C _), funext (moss₁ C u W), funext (moss₁ C v W), funext (mud₁ C u v W),ride_zero,zero_mul,add_zero,add_mul]; simp only [upL,mul_assoc]
lemma royal (t:Site n)(W:Bloom 2)(u v:Weather n): dig u v (silt C t W) 0= rides (Equiv.refl _) (fun x=> jewels x W u v • bloomC C W) * routeM t 1 W.tail:=by
  let f (z:Weather n):= rides (Equiv.refl _) (blossom C W z); have hf : Differentiable ℂ f:= (gate n).differentiable.comp (spurs C _)
  change dig u v (fun z=> f z*amass C t W.tail z) 0= _; rw [drip_prod hf (hooked C t _),show f 0=0 from (by unfold f; rw [leafZero C (by decide) W]; exact ride_zero _),zero_mul]
  unfold f; rw [drip_gate _ (spurs C _),drip_gate _ (spurs C _),dive_gate _ (spurs C _), funext (moss₂ C u W),funext (moss₂ C v W),funext (mud₂ C u v W)]; simp [ride_zero,amass0] -- check
end YM.QCD.Pearl
