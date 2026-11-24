import YM.QCD.Pearl.Polish

/-! # physical velocity isotope -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Pearl
open Lat Cost Lattice Wilson Function Filter Finset Kit Pine Flume Laurent Bloch Metric YM.Next.Free RG Rudder Revolve Free Para
open scoped Matrix Matrix.Norms.L2Operator BigOperators Topology ContDiff
variable {n:Side}{I J D:Type}{p:Site n}{z:Momentum}{j : ℕ}
lemma crystal_eye {f : I→Momentum→ℂ} {w}(h: Moderate w f)(i):DifferentiableAt ℂ (f i) 0:= by obtain ⟨z,C,hz,hC,H⟩:= h; exact (H i).hol 0 (cube_zero _ hz)
lemma iris {f : I→Momentum→Para} {w}(h:Scale w f)(i):DifferentiableAt ℂ (f i) 0:= (crystal_eye h.scalar i).prodMk (differentiableAt_pi.mpr (fun k=> crystal_eye (h.vector k) i))
lemma key_0 (v:Train j):key v 0=1:=by simp [key,tall,alias_zero_eq,narrow]
lemma gramVelocity (k : Momentum): dew k Flume.kernel 0=(0,k):=by
  have he:HasDerivAt (fun u:ℂ=> Flume.kernel (u • k)) ((0,k):Para) 0:=by
    have ht a: HasDerivAt (fun u:ℂ=> u*k a) (k a) 0:=by simpa using ((hasDerivAt_id' (0:ℂ)).mul_const (k a))
    have hh a: HasDerivAt (fun u:ℂ=> 1- Complex.cos (u*k a)) 0 0:=by simpa using! ((hasDerivAt_const (0:ℂ) (1:ℂ)).sub ((ht a).ccos))
    have hp a: HasDerivAt (fun u:ℂ=> Complex.sin (u*k a)) (k a) 0:=by simpa using! (ht a).csin
    have hy:= HasDerivAt.fun_sum (u:=univ) (fun i _=> hh i); rw [sum_const_zero] at hy
    exact hy.prodMk (hasDerivAt_pi.mpr hp)
  have hv: HasDerivAt (fun u:ℂ=>u • k) k 0:=by simpa using! ((hasDerivAt_id' (0:ℂ)).smul_const k)
  have hx:DifferentiableAt ℂ Flume.kernel (0:Momentum):=by unfold Flume.kernel; fun_prop -- check
  have hm:= (show (0:ℂ) • k=(0:Momentum) from zero_smul ..); have hb:= (show DifferentiableAt ℂ Flume.kernel ((0:ℂ) • k) from hm ▸ hx).hasFDerivAt.comp_hasDerivAt (0:ℂ) hv; rw [hm] at hb; exact hb.unique he
lemma peg_vel (v:Train j)(k:Momentum): dew k (peg v) 0=(0,k):=by
  let f (p:Momentum):=(v.mass.val:ℂ)⁻¹ • p
  let L:Momentum→L[ℂ] Momentum:= (v.mass.val:ℂ)⁻¹ • ContinuousLinearMap.id ℂ _
  have hx:DifferentiableAt ℂ Flume.kernel (0:Momentum):=by unfold Flume.kernel; fun_prop
  rw [show peg v=(fun p=> (v.mass.val:ℂ) • (Flume.kernel ∘ L) p) from ?_];
  · have ht:DifferentiableAt ℂ Flume.kernel (L 0):=by rw [map_zero]; exact hx
    rw [dew_s (differentiableAt_const _) (ht.comp (f:=L) _ L.differentiableAt),dew_chain L.differentiableAt ht,dewp,map_zero,dew_zero,zero_smul,add_zero,gramVelocity]; ext <;> simp [L]
  funext p; rw [comp_apply,Flume.peg,tiny,alias_zero_eq]; congr 2
lemma steamP {v:Train j} (hj : 2≤j) (k:Momentum): dew k (Dir v) 0=(0,k):=by
  have hk: DifferentiableAt ℂ (key v) 0:= crystal_eye (key_upper (fun _:Unit=>v)) ()
  have hx: DifferentiableAt ℂ (peg v) 0:= iris (pegs (fun _:Unit=>v)) ()
  have hv: DifferentiableAt ℂ (chipper v) 0:= crystal_eye ((pegs (fun _:Unit=>v)).squares) ()
  have hz : chipper v 0=0:=by simp [chipper,pen]
  let L:Para→L[ℂ] Para:= LinearMap.toContinuousLinearMap {toFun:=turn,map_add':=fun x y=> by ext <;> simp [turn,add_comm],map_smul':=fun p x=>by ext <;> simp [turn]}
  have ht : dew k (chipper v) 0=0:=by
    have he:= (Dir_budget hj (fun _:Unit=>v)).vector
    -- chain beam
    have hf : Differentiable ℂ Para.quad := by unfold Para.quad; fun_prop
    rw [show chipper v=Para.quad ∘ peg v from rfl,dew_chain hx (hf _),pen,peg_vel]
    let X:Para:=(0,k)
    have hU: HasDerivAt (fun u:ℂ=> u • X) X 0:=by simpa using! ((hasDerivAt_id' (0:ℂ)).smul_const X)
    have he:= (hf ((0:ℂ) • X)).hasFDerivAt.comp_hasDerivAt (0:ℂ) hU; have hy : HasDerivAt (fun u:ℂ=> Para.quad (u • X)) 0 0:=by simp_rw [Para.quad_smul]; simpa using! (((hasDerivAt_pow 2 (0:ℂ)).mul_const (Para.quad X)))
    rw [zero_smul] at he; exact he.unique hy
  have hd:DifferentiableAt ℂ (fun p=> (den v p)⁻¹) 0:= (crystal_eye (d_house hj (fun _:Unit=>v)) ()).inv (by change den v 0≠0; rw [den_origin]; exact one_ne_zero)
  have hu:DifferentiableAt ℂ (L ∘ peg v) 0:= L.differentiableAt.comp _ hx
  have hh: DifferentiableAt ℂ (rest v) 0:= iris (remainder hj (fun _:Unit=>v)) ()
  have hT: dew k (nume v) 0=L (0,k):=by
    rw [show nume v=(fun p=> key v p • (L ∘ peg v) p)+(fun p=>chipper v p • rest v p) from rfl]; rw [dew_plus (hk.fun_smul hu) (hv.fun_smul hh),dew_s hk hu,dew_s hv hh, Function.comp_apply,pen,map_zero, hz,ht, smul_zero,zero_smul,zero_smul, add_zero, add_zero,add_zero,key_0,one_smul]; rw [dew_chain hx L.differentiableAt,dewp,peg_vel]
  have hX:DifferentiableAt ℂ (nume v) 0:= iris (n_house hj (fun _:Unit=>v)) ()
  rw [show Dir v= (fun p=> (den v p)⁻¹ • (L ∘ nume v) p) from rfl]; rw [dew_s hd (L.differentiableAt.comp _ hX),dew_chain hX L.differentiableAt,dewp,hT,den_origin, Function.comp_apply,show nume v 0=0 by simp [nume,hz,pen,turn],map_zero, smul_zero, add_zero,inv_one,one_smul]; exact turn_turn _
lemma gust_v (v: Train j) (hj:2≤j)(x:Momentum): dew x (fun p=> model (Dir v p)) 0=Complex.I • hiss x:=by
  let L: Para→L[ℂ] Bundle:= Para.signal.toContinuousLinearMap; rw [show (fun p=> model (Dir v p))=(L ∘ Dir v) from rfl,dew_chain (show DifferentiableAt ℂ _ _ from iris (Dir_budget hj (fun _:Unit=>v)) ()) L.differentiableAt,dewp,steamP hj]; change model (0,x) = _; rw [model]; simp
end YM.QCD.Pearl
