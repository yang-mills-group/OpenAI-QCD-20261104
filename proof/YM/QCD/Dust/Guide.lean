import YM.QCD.Dust.Scallop
/-! # pricing kernel parallel transport response on BRICK weights. Two heights with fee. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Dust
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run Brick
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Push.Uniform Planned.AtomRegular
open scoped Matrix.Norms.Frobenius ContDiff in
lemma entry_ω (i j:Hue): ContDiff ℝ ω (fun x:su.Color=>colour (su.lieExp x) i j):= by
   let W:su.Mat→L[ℝ]ℂ:=LinearMap.toContinuousLinearMap { toFun:=fun x=> x i j,map_add':=fun i j=>rfl,map_smul':=fun i j=>rfl }
   exact W.contDiff.comp su.exp_jet
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
open Garden Fork Leaf Tee Flume YM.Next.Free Laurent Reggae
open PhysicalNext.JointLoad MultiNext.SignedSource AnalyticBridge.SectorAffine.Offset
variable {c f L:Side} {j k N n:ℕ} {C K h1 h2 u v w t:ℝ} {o:Site f}{p r:ℝ}{Q:Kit.Rail f c}
local notation "A"=> Crate f N

variable {a: Site c}
section light
variable {E D I:Type}[NormedAddCommGroup E][NormedSpace ℝ E] [NormedAddCommGroup D][NormedSpace ℝ D][NormedAddCommGroup I][NormedSpace ℝ I]
lemma jersey (g:E→D)(f:D→I)(p':E)(hp: Through n g p' v) (h:∀ z,‖z‖≤1→Through n f z C)(hv:v≤1)(hn:1≤n)(hh:f 0=0): Through n (f ∘ g) p' ((1+patterns n)*(C*v)):=by
   have ht : ‖g p'‖ ≤ v:= by simpa only [norm_iteratedFDeriv_zero] using hp.pay 0 (Nat.zero_le _)
   have hF:= h (g p') (ht.trans hv); have hx :=hp.nonneg; have hC:=hF.nonneg
   refine ⟨hF.smooth.comp _ hp.smooth,fun q hq=>?_⟩; by_cases he:q=0
   · subst q; rw [norm_iteratedFDeriv_zero,Function.comp_apply]; exact (Heir.locate (x:=g p') h hn hh (ht.trans hv)).trans ((mul_le_mul_of_nonneg_left ht hC).trans (le_mul_of_one_le_left (by positivity) (by linarith [patterns_nonneg n]))) -- namespaces
   refine (slots_bound hp.smooth hF.smooth hq (C:=C*v) (by positivity) (fun p w hw=>?_)).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (by positivity))
   let G i:= iteratedFDeriv ℝ (p.partSize i) g p' (fun j=>w (p.emb i j))
   have he(i):‖G i‖ ≤ v:= by simpa only [G,Finset.prod_const_one,mul_one] using ContinuousMultilinearMap.le_mul_prod_of_opNorm_le_of_le (hp.pay (p.partSize i) ((p.partSize_le _).trans hq)) (fun j=>hw (p.emb i j))
   apply le_trans (ContinuousMultilinearMap.le_mul_prod_of_opNorm_le_of_le (hF.pay p.length (p.length_le.trans hq)) he)
   rw [Finset.prod_const,card_univ,Fintype.card_fin]; apply mul_le_mul_of_nonneg_left _ hC; exact (pow_le_pow_of_le_one hx hv (p.length_pos (by omega))).trans_eq (pow_one _)
end light
-- transfer roots
lemma heli (n:ℕ): ∃ c:ℝ,∀ (f:Side)(Y: Site f → su.Color), ‖Y‖ ≤1 → Through n (pulseQ f) Y c:=by
   let H (x:su.Color):=Lat.touch (colour (su.lieExp x)); have hp: ContDiff ℝ ω H:=by
      let v(x:su.Color):=colour (su.lieExp x)
      let W : ((i j:Hue)→ℂ)→L[ℝ]Mat := LinearMap.toContinuousLinearMap { toFun:=Matrix.of,map_add':=fun i j=>rfl,map_smul':=fun i j=>rfl }
      let p (x:su.Color)(i j:Hue):=v x i j; have hp:ContDiff ℝ ω p:=by refine contDiff_pi.mpr (fun i=> contDiff_pi.mpr fun j=>?_); exact entry_ω i j
      exact Stew.silverW.contDiff.comp (f:=W ∘ p) (W.contDiff.comp hp)
   obtain ⟨C,hC,h⟩:= exists_allows (f:=H) (isCompact_closedBall 0 1) (fun _ _=>hp.contDiffAt) n
   refine ⟨C,fun f X he=>?_⟩
   have hh (i:Site f):Through n (fun x:Site f→su.Color=> H (x i)) X C:=by
       let L:= ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Site f=> su.Color) i
       refine Heir.pre_through (f:=H) L (ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun j=>?_ ) X (Through.control (h (L X) (mem_closedBall_zero_iff.mpr ((norm_le_pi_norm X i).trans he))))
       rw [one_mul]; exact norm_le_pi_norm j i
   apply Heir.pair_through (Heir.pi_through (f:=fun i j=> (pulseQ f i).1 j) hC (fun i=> hh i))
   apply Heir.pi_through hC; intro i; let S:= (starL' ℝ: Bundle≃L[ℝ] Bundle).toContinuousLinearMap; have he': (fun x:Site f→su.Color=> (pulseQ f x).2 i)=S ∘ (fun x=>H (x i)):=by funext x; unfold pulseQ ramp; simp only [colour_inv]; exact (Lat.touch_star _).symm
   change Through n (fun y:Site f→su.Color=> (pulseQ f y).2 i) X C; rw [he']; have he : Through n _ X (1*C):= Heir.linear_through S (hh i) (ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x=>by change ‖star x‖≤_; rw [norm_star,one_mul])) -- S
   rw [one_mul] at he -- failing syntax
   exact he
lemma mantle (p h:ℝ)(hp:0<p) (ht:0<h)(hv:fareG 2 p N ≤ h)(hA:∀ i:A,Stew.plank a u (apple Q N i) ≤ Stew.plank o p i) (y:Site f→su.Color)(hv':‖y‖ ≤1) (hr : Through n (pulseQ f) y t):
       let M z:= merchant a o Q u h ht z N; let F x:= M (pulseQ f x) - M (pulseQ f 0)
       Through n F y (composeCost n (1*((1+(2:ℝ)^n/1)^n)) t+1):=by
    intro M F; have hp(x:Site f→su.Color): ‖pulseQ f x‖ ≤1:= royal _
    have h(z:Site f→su.Color): Allows n M (pulseQ f z) (1*((1+(2:ℝ)^n/1)^n)) :=by
       refine allows_real_of_entire n (f:=M) (stupor ht) zero_lt_one (fun x hx=>?_); apply creditB x (by assumption) ht (by norm_num) _ hv hA; have hR:‖x-pulseQ f z‖≤1:=by rw [← dist_eq_norm]; exact (Metric.mem_ball.mp hx).le
       exact (show ‖x‖≤ ‖x-pulseQ f z‖+‖pulseQ f z‖ by simpa using norm_sub_le_norm_sub_add_norm_sub x (pulseQ f z) 0).trans (by linarith [hp z]) -- hp shadow
    let W:= M (pulseQ f 0); have hh: Through n (fun _ : Site f → su.Color=> -W) y 1:= Through.control (allows_const _ (show ‖-W‖ ≤1 from (norm_neg _).trans_le (creditB _ (by assumption) ht (by norm_num) ((hp 0).trans (by norm_num : (1:ℝ) ≤ 2)) hv hA)))
    have hT : F= (M ∘ pulseQ f)+(fun _=>-W):= funext fun i=> sub_eq_add_neg ..
    rw [hT]; exact Heir.sum_through ((Through.control (h y)).comp hr) hh
end YM.QCD.Dust
