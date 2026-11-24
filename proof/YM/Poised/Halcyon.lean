import YM.Poised.Cabin
/-!
# Torus filtration cancellation, true through any weight
TE condition costs next.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open Function Filter Lattice Wilson RG Source Source.Drops MeasureTheory Finset WardBin Work.G05 Planned.PrimaryIntegral295 Planned.PrimaryIntegral295.Place
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius TensorProduct Classical ComplexConjugate
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead
variable {B : Type}[Fintype B]{d a k n:ℕ}{c:Side}
namespace Pipes
open Beacon Gem MultiNext.SignedSource YM.Next.Foundations QCD.Cove QCD.Creek
variable (T:Taper) (b:Cover) -- remove V
abbrev lotsF (F:Grid c→ Lat.Fields c 6) (x: Path c B): Alg B:= changeVars x.2 (F (increment 1 x.1))
abbrev Rooted (V:Support c)(F:Grid c → Lat.Fields c 6):= LocalOn V F ∧ ∀ u:Grid c, F u ∈ region (Cove.limits (F:=6) V)
lemma life (x:Site c×Shell) : Cove.locationP (stretch _ x)=x.1:=by obtain ⟨x,h|h⟩:=x <;> rfl
lemma life_mem (x:Site c) (j:Shell)(V: Support c): stretch _ (x,j)∈ Cove.limits (F:=6) V↔x∈V:=by simp only [Cove.limits,mem_filter,mem_univ,true_and]; rw [life]
lemma chordX (x y: Path c B)(V: Support c) (h:∀ i∈V,asks x.2 i=asks y.2 i) (i) (hi:i∈Cove.limits (F:=6) V): x.2 i=y.2 i:=by
   obtain ⟨⟨z,j⟩,rfl⟩:= (stretch (Site c)).surjective i; exact congr_fun (h z ((life_mem ..).1 hi)) j
lemma localP (x y: Path c B)(V: Support c)(F:Grid c→ Lat.Fields c 6)(hf:Rooted V F)(hx:Glazed x y V) : lotsF F x=lotsF F y:=by
    unfold lotsF; rw [hf.1 _ (increment 1 y.1) (fun i ht hv=>by rw [increment, increment,hx.H i ⟨ht,hv⟩])]
    let U:=Cove.limits (F:=6) V; let K:=embed (fun i:↥U=>i.val); obtain ⟨z,hZ⟩:=hf.2 (increment 1 y.1)
    rw [←hZ]; change ((changeVars x.2).comp K) z=((changeVars y.2).comp K) z; exact congr_arg (fun f:_ →ₐ[ℂ]_=>f z) (ext_atoms fun i=>by simp only [AlgHom.comp_apply,K,embed_atom,change_atom,chordX x y V hx.S0 i.val i.property])
lemma lots_alive (F:Grid c→ Lat.Fields c 6)(hf:ContDiffAt ℝ d (F ∘ increment 1) 0): ContDiffAt ℝ d (lotsF (B:=B) F) 0:=aperture _ Prod.snd (0:Path c B) _ (hf.comp (f:=Prod.fst (α:=Directions su c) (β:= VectorD (Site c) B)) (0:Path c B) contDiffAt_fst) contDiffAt_snd
lemma melody (V:Support c) (F:Grid c→ Lat.Fields c 6)(he:Rooted V F)(x y:Fin n→ Path c B)(hx:∀ i,Glazed (x i) (y i) V)(hf: ContDiffAt ℝ n (F ∘ increment 1) 0): iteratedFDeriv ℝ n (lotsF F) 0 x=iteratedFDeriv ℝ n (lotsF F) 0 y:=by
    let P:VectorD (Site c) B →L[ℝ] VectorD (Site c) B:= ContinuousLinearMap.pi fun i=> if i∈Cove.limits (F:=6) V then ContinuousLinearMap.proj i else 0
    let G:= (Mom.screen (G:=su) V).prodMap P; let f:=lotsF (B:=B) F
    have hh(i) (v:Path c B): (G v).2 i= if i∈Cove.limits (F:=6) V then v.2 i else 0:=by change P v.2 i=_; simp only [P,ContinuousLinearMap.pi_apply]; split <;> rfl
    have h : f=f ∘ G:= funext fun i=>localP i (G i) V F he ⟨fun j h=>by change _=Mom.screen V i.1 j; rw [Mom.screen_at,if_pos h],fun j hj=>funext fun v=>by unfold asks; rw [hh,if_pos ((life_mem ..).2 hj)]⟩
    let q:=iteratedFDeriv ℝ n f 0; have ht:q=q.compContinuousLinearMap (fun _=> G):=calc _=iteratedFDeriv ℝ n (f ∘ G) 0:= congr_arg (fun Z=> iteratedFDeriv ℝ n Z 0) h
                                                                                         _=_:=jets_linear G (lots_alive F hf)
    have hu(i):G (x i)= G (y i):=by
       apply Prod.ext
       · funext j; change Mom.screen V (x i).1 j=Mom.screen V (y i).1 j; rw [Mom.screen_at,Mom.screen_at]; split; next h=> exact (hx i).H j h
         next _=>rfl
       funext j; rw [hh,hh]; split; next h=> exact chordX (x i) (y i) V (hx i).S0 _ h
       next _=>rfl
    change q x=q y; rw [ht]; change q (fun i=>G (x i))=q fun i=>G (y i); simp_rw [hu]
variable (H:TaperHol)(V:Support c)(hx:Nonwrapping V (wrap c b))(hV:100 ≤ c.val)
include hx hV
local instance : NormedSpace ℝ (Book c B d):=inferInstance
set_option synthInstance.maxHeartbeats 300000
set_option maxHeartbeats 770000
lemma cancels (F:Grid c→ Lat.Fields c 6)(he:Rooted V F)(hg:∀ k U,slots 6 k (F (gauge k U))=F U)(hf: ContDiffAt ℝ d (F∘increment 1) 0)(k:ℕ)(hk:k ≤ d+1)(h:∀ (J:Labels.Jet su)(t:ℕ),t<k→ leading t (moment (d:=d) H b J F)=0) (X:Fin n→ Path c B)(w : Fin n→ℕ)(hw:∀ i, 2 ≤ w i)(hW:∑ i,w i<k)(hv:∀ i,Buoyant (X i) V b (w i)): iteratedFDeriv ℝ n (lotsF F) 0 X=0:=by
   induction n using Nat.strong_induction_on with
   | h n ih =>
      have heV : (∑ i,w i)≤d := Nat.le_of_lt_succ (lt_of_lt_of_le hW hk)
      choose f hF hY using fun i=>issued H.T b hx hV (X i) (w i) ((Finset.single_le_sum (f:=w) (fun i _=> Nat.zero_le _) (Finset.mem_univ i)).trans heV) (hv i)
      have hl : n ≤ d:= (Cases.arity (fun i=> (show 0 < w i from Nat.lt_of_lt_of_le (by omega : 0 < 2) (hw i)))).trans heV
      let A:=lotsF (B:=B) F; let R:Book c B d→ Path c B:= enroll H.T b; let P:=play H b F (B:=B) (d:=d); let L:Book c B d →L[ℝ] Marker B d:= ContinuousLinearMap.snd ℝ _ _
      have hxB:P ∘ L=ᶠ[𝓝 0] A ∘ R:=by
         filter_upwards [incAt b hx hV H (d:=d) (B:=B)] with y hy
         change changeVars _ (F (views H b d y.2.1))= changeVars _ (F _); rw [he.1 _ _ hy, ← hg (sealsZ y.1) (views H b d y.2.1)]; symm; exact AlgHom.congr_fun (change_mul _ _) _
      have hb:= seal_zero H.T b (c:=c) (d:=d) (B:=B)
      have ha : iteratedFDeriv ℝ n (A∘R) 0 f=0:=by
         have he := jets_linear L (show ContDiffAt ℝ n P 0 from (live_play b H F hf).of_le (Nat.cast_le.mpr hl))
         have ht := (hxB.iteratedFDeriv ℝ n).eq_of_nhds
         exact (DFunLike.congr_fun (ht.symm.trans he) f).trans (exalt b H F hf h hk w hW hl (fun i=>(f i).2) (fun i=>(hF i).H) (fun i=>(hF i).S0))
      rw [Cases.compReads (hb.symm ▸ lots_alive F hf) ((seal_live H.T b).of_le le_top) (Nat.cast_le.mpr hl) f, sum_eq_single (.atomic n)] at ha
      · rw [Cases.one,hb] at ha; exact (melody V F he X _ hY (hf.of_le (Nat.cast_le.mpr hl))).trans ha
      · intro p _ hp; have hz:= Cases.all p w; let r:=Cases.costs p w; unfold Cases.caseRead; rw [hb]; refine ih _ (lt_of_le_of_ne p.length_le (fun he=>hp (Cases.finest p he))) _ r (fun i=>?_) (hz.trans_lt hW) (fun i=> ordinance H.T b hx hV (f ∘ p.emb i) (w ∘ p.emb i) (fun j=> hF _) fun j=>hw _)
        let q: Fin (p.partSize i):=⟨0,p.partSize_pos _⟩; exact (hw (p.emb i q)).trans (single_le_sum (f:=fun j=>w (p.emb i j)) (fun i _=> Nat.zero_le _) (mem_univ q))
      simp
end Pipes
end YM.Massive.Poised
#print axioms YM.Massive.Poised.Pipes.cancels
