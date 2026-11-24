import YM.Siro.Lapis
set_option maxHeartbeats 460000
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Siro
open Metric Function Set Filter Analysis
open Ward (Latest Earliest)
open Fields (pointMoment distinct)
open scoped Topology InnerProductSpace ContDiff Classical BigOperators
variable {F:Fields}{n:ℕ}{S:F.Kernel}(H:Brawl S)
lemma emits (x:Points n)(i:Fin n)(p:Fin n→ F.W)(b:Axis):∃ l r: Cluster F,(∀ s:ℝ, realize p (Ward.cast x i b s)= l++ (YM.Ward.inc b (x i) s,p i)::r) ∧ ∀ v∈l++r, ∃ j:Fin n,j≠i ∧ v=(x j,p j):=by
    induction n with
    | zero=>exact Fin.elim0 i
    | succ n ih=>
          refine Fin.cases ?_ (fun j=>?_) i
          · let A:=realize (F:=F) (fun k:Fin n=>p k.succ) (Points.tail x); refine ⟨[],A,fun s=>?_,?_⟩
            · rw[Ward.tip]; unfold realize; rw[List.ofFn_succ]; rfl
            intro v hv; change v∈A at hv; obtain ⟨j,rfl⟩:= List.mem_ofFn.mp hv; exact ⟨j.succ,j.succ_ne_zero,rfl⟩
          obtain ⟨l,r,hl,hr⟩:= ih (Points.tail x) j (fun k=>p k.succ); refine ⟨(x 0,p 0)::l,r,fun s=>?_,?_⟩
          · unfold realize at *; rw [List.ofFn_succ]; simp only[Ward.near x j.succ 0 (Ne.symm j.succ_ne_zero)]; congr 1; change _=l++ (Ward.inc _ _ _, p j.succ)::r; rw[←show List.ofFn _=l++ (Ward.inc b (x j.succ) s,p j.succ)::r from hl s]; apply congr_arg; funext k; by_cases ht:k=j
            · subst k; exact Prod.ext (by rw[Ward.atCast,Ward.atCast]; rfl) rfl
            exact Prod.ext (by rw [Ward.near x j.succ _ (fun h=>ht (Fin.succ_inj.mp h)),Ward.near _ _ k ht]; rfl) rfl
          intro y hy; rcases List.mem_cons.mp (show y∈ (x 0,p 0)::(l++r) from hy) with rfl|hm; · exact ⟨0,j.succ_ne_zero.symm,rfl⟩
          obtain ⟨k,hk,hx⟩:= hr _ hm; exact ⟨k.succ,fun h=>hk (Fin.succ_inj.mp h),hx⟩
include H
lemma spurs (x:Points n)(i:Fin n)(p:Fin n→ F.W)(a b:Axis)(s:ℝ)(h: Latest (Ward.cast x i b s) a i) : AnalyticAt ℝ (readQ S p ∘ Ward.cast x i b) s:=by
     obtain ⟨V⟩:= realization H.toSimpleK (H.adj_flip a)
     obtain ⟨l,r,hl,hr⟩:= emits x i p b; have hp: distinct (realize (F:=F) p (Ward.cast x i b s)):= (realized ..).mpr h.1
     rw[hl,locations] at hp
     let u(y:ℝ): Plant F:= (Ward.inc b (x i) y,p i)
     apply AnalyticAt.congr (whole V H _ b l r (p i) s _ _); · exact Eventually.of_forall fun y=> by dsimp only; rw[←hl,readAt]; rfl
     · rw[locations]; exact hp.sublist (((List.Sublist.cons (u s) (List.Sublist.refl r)).append_left l).map Prod.fst)
     intro y hy; obtain ⟨j,hj,rfl⟩:= hr y hy; have ht:=h.2 j hj; rw [Ward.near x i j hj,Ward.atCast] at ht; exact ht
-- reflection mirror discrete
omit H in
private lemma spiegel (x : Points n) (i : Fin n) (a b : Axis) (t : ℝ) :
    Points.move (Signed.reflect a) (Ward.cast x i b t)=Ward.cast (Points.move (Signed.reflect a) x) i b (if b=a then -t else t) := by
  apply PiLp.ext; intro k; simp only [Ward.cast,Points.move_coord,PiLp.add_apply,PiLp.smul_apply]; rw [show Ortho.move _ (_+_)=_ from (Ortho.motion _).map_add _ _]; congr 1; by_cases h : k=i
  · subst k; ext j; simp [Signed.mirrored,Points.direction]; split_ifs <;> simp_all
  simp [Points.direction,h, Signed.ortho_move,Signed.reflect]
lemma purred(x: Points n)(i:Fin n)(p:Fin n→ F.W)(a b:Axis)(s:ℝ)(h:Earliest (Ward.cast x i b s) a i): AnalyticAt ℝ (readQ S p ∘ Ward.cast x i b) s:=by
     obtain ⟨f,hf⟩:= H.mirror a
     let Z:= Points.move (n:=n) (Signed.reflect a); let d(u:ℝ):= if b=a then -u else u
     have hh: Latest (Ward.cast (Z x) i b (d s)) a i:= by
             rw[show Ward.cast _ _ _ _=Z (Ward.cast x i b s) from (spiegel (x:=x) i a b s).symm]; exact ⟨Points.move_in _ h.1,fun j hi=>by simpa[Z,Signed.mirrored] using h.2 _ hi⟩
     have ht : AnalyticAt ℝ d s:=by by_cases he:b=a; rw [show d= -id from funext fun i=>by simp [d,he]]; apply analyticAt_id.neg; rw [show d=id from funext fun i=>by simp[d,he]]; exact analyticAt_id
     apply ((spurs H (Z x) i (f∘p) _ _ _ hh).comp ht).congr
     filter_upwards[(Ward.moves x i b s).continuousAt.preimage_mem_nhds ((conf_open _).mem_nhds h.1)] with i' hi
     change readQ S (⇑f ∘ p) (Ward.cast (Z x) i b (d i'))= _; rw [show Ward.cast _ _ _ _=Z (Ward.cast x i b i') from (spiegel (x:=x) i a b i').symm]; exact (hf n p _ hi).symm
lemma channel (x:Points n)(p:Fin n→F.W)(K:Ortho.Skew)(k:Fin n)(a b:Axis)(s:ℝ)(hv:Earliest (Ward.cast x k b s) a k ∨ Latest (Ward.cast x k b s) a k):AnalyticAt ℝ (angQ S p K ∘ Ward.cast x k b) s:=by
     have he(i:Fin n→F.W):ContDiffAt ℝ ω (readQ S i∘ Ward.cast x k b) s:=AnalyticAt.contDiffAt (hv.elim (purred H x k i a b s) (spurs H x k i a b s)) -- .. may issue
     apply ContDiffAt.analyticAt; unfold Function.comp angQ; apply ContDiffAt.sum; intro i hi; apply (he _).add (ContDiffAt.sum _)
     intro u hu; have ht:ContDiffAt ℝ ω (Ward.cast x k b) s:= contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const); exact ((Ward.factor i u K).contDiff.contDiffAt.comp s ht).smul (he _)
omit H
private lemma unique {f : ℝ → ℂ} {a : ℝ} (h : AnalyticAt ℝ f a) (he : ∀ n, iteratedDeriv n f a=0) :
    f =ᶠ[𝓝 a] 0 := by
  obtain ⟨p,r,hp⟩ := h
  have H n : p n=0 := by
    apply ContinuousMultilinearMap.ext; intro x
    rw [FormalMultilinearSeries.apply_eq_prod_smul_coeff]
    have ht := hp.factorial_smul 1 n
    rw [← iteratedDeriv_eq_iteratedFDeriv,he,← Nat.cast_smul_eq_nsmul ℝ] at ht
    have hh : p.coeff n=0 := (smul_eq_zero_iff_right (by positivity : (Nat.factorial n:ℝ)≠0)).mp ht
    rw [hh,smul_zero];rfl
  filter_upwards [eball_mem_nhds a hp.r_pos] with t ht
  have hw := hp.hasSum (y := t-a) (show _ from by
    rw [mem_eball, ← edist_sub_right t a a, sub_self] at ht; exact ht)
  simp only [H,_root_.zero_apply,add_sub_cancel] at hw
  exact hw.unique hasSum_zero

def Still {F:Fields}(S:F.Kernel)(x:Points n):= ∀ p K,angQ S p K x=0
include H
lemma stood {a:Axis}(x : Points n) (k : Fin n) (b) (u v : ℝ) (h : ∀ i∈uIcc u v, Earliest (Ward.cast x k b i) a k ∨ Latest (Ward.cast x k b i) a k)
    (hp : Still S (Ward.cast x k b v)) : Still S (Ward.cast x k b u) := by
  let z := Ward.cast x k b; have hU := right_mem_uIcc (a := u) (b := v); have hv := h _ hU; have hz : z v∈conf _ := hv.elim And.left And.left
  intro p g; let f := angQ S p g ∘ z; have hh : AnalyticOnNhd ℝ f (uIcc u v) := fun i hi => channel H x p g k _ b i (h _ hi); have he := unique (hh v hU) (fun m => jet_line H g p x k b v hz (fun w => hp w g) m)
  exact (hh.eqOn_zero_of_preconnected_of_eventuallyEq_zero (isPreconnected_uIcc) hU he) left_mem_uIcc
lemma along {x y: Points n}(h: Ward.Walk n x y)(hv:Still S y): Still S x :=by
     induction h with
     | id=>exact hv
     | bridge x i a b s hp => simpa only [Ward.start] using stood H _ _ _ _ _ hp hv
     | transit _ _ ih im=>exact ih (im hv)
omit H
open Ward (arranged)
private lemma fills (a:Axis) (x : Points n) : x∈closure {x : Points n | arranged a x} := by
  let v := points fun i : Fin n => (↑(i.val):ℝ) • basis a
  let z := fun t : ℝ => x+t • v
  have he : Tendsto z (𝓝[>] 0) (𝓝 x) := by
    have h : Continuous z := continuous_const.add (continuous_id.smul continuous_const)
    simpa [z] using (h.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  have hu : ∀ᶠ t in 𝓝[>] 0, ∀ i j, i≠j → z t i a≠ z t j a := by
    apply eventually_all.mpr; intro i; apply eventually_all.mpr; intro j
    by_cases h : i=j
    · exact Eventually.of_forall fun _ hx => (hx h).elim
    have hh : (i.val:ℝ)≠j.val := by exact_mod_cast (show i.val≠j.val from fun p => h (Fin.ext p))
    by_cases hi : x i a=x j a
    · filter_upwards [self_mem_nhdsWithin] with t ht Hh
      have hr : t≠0 := LT.lt.ne' ht
      simp [z,v,hi,hr]; exact fun hy => h (Fin.ext hy)
    have hp := he.eventually (show ({x : Points n | x i a ≠ x j a} : Set _) ∈ _ from
      (isOpen_ne_fun (by fun_prop : Continuous (fun x : Points n => x i a)) (by fun_prop)).mem_nhds hi)
    exact hp.mono fun x h _ => h
  apply mem_closure_of_tendsto he (hu.mono fun i hi => show arranged a (z i) from fun j k h => by_contra fun hg => hi j k hg h)

include H
lemma opened (x : Points n) (hx : x∈conf n) : Still S x := by
  let a : Axis := 0; let b : Axis := 1
  have he i (h : arranged (n := n) a i) : Still S i := by
    obtain ⟨p,ht,hP,ha⟩ := Ward.line a b (by norm_num [a,b]) i h Finset.univ (by simp)
    exact along H ht (fun k g => H.line _ k _ _ a ha hP)
  obtain ⟨f,hf,hv⟩ := mem_closure_iff_seq_limit.mp (fills a x)
  intro q K
  have ht := (axe H hx K q).continuousAt.tendsto.comp hv
  exact tendsto_nhds_unique ht (tendsto_const_nhds.congr (fun i => (he _ (hf i) q K).symm))
end YM.Massive.Siro
#print axioms YM.Massive.Siro.opened
