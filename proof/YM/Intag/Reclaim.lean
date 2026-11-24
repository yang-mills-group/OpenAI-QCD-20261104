import YM.Intag.Clover
/-! # Universal mark comparison.Quills.A true Wick geometry.Unused-label-independent.Magnitude-critical -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Sample.Quills
open QCD QCD.Grass QCD.Creek QCD.Cove Function Finset Filter NormedSpace
open MassiveQCD.Ribbon MassiveQCD.Play MassiveQCD.Play.Chamber Apron Cupola
open scoped Topology ContDiff BigOperators Classical TensorProduct Matrix.Norms.L2Operator
open YM.Arise.Bill YM.Arise.Count YM.Massive YM.Massive.UV Quills.Eden
variable {A B I J:Type}[Fintype A][Fintype B][Fintype I][Fintype J]{n:ℕ}
namespace Clover
variable (Q:I→Bool)(W:J→Bool)(u:I↪ J)(h:∀ i,W (u i)=Q i)
variable (S: Matrix (Spine I) (Spine J) ℂ)(hs:∀ i:I,changeVars S (mono (burst Q {i}))=mono (burst W {u i}))
local notation "λJ"=> jetP A S
variable (s: Fin n→ I)
local notation "g"=> u∘s
variable (v:J→ℕ)(P: ∀ i:I, Arise.Bill.Cups (v (u i)) (Q i))(P': ∀ i:J, Arise.Bill.Cups (v i) (W i)) (p:I→ E4) (p':J→E4)
local notation "Z"=> pays (U:=A) Q (v ∘u) p P
local notation "Z'"=> pays (U:=A) W v p' P'
variable (T:Finset I)(ht:Set.InjOn p T) (hm:∀ i∈ T,p' (u i)= p i) (hΦ:∀ i∈T, Arise.Bill.meaning (v (u i)) (W (u i)) (P' (u i))= Arise.Bill.meaning (v (u i)) (Q i) (P i))
-- natural mapping marks. Momentum facts all because Wick construction.L.
include hm hΦ ht hs
lemma inherited(t:Finset I)(h:t⊆T): jetP A S ((Z) t)= (Z') (t.map u):=by
     let f:= Quills.tour t; have hf:crest f=t:=Quills.club _; have hk(j):f j∈T:=h (hf ▸ (exists_fix ..).2 ⟨j,rfl⟩)
     let F:= u∘f; have hu: p' ∘ F=p∘f:=funext fun i=>hm _ (hk i); have hx:points (p∘f)∈conf t.card:= fun i j he=>snug t (ht (hk _) (hk _) he); have hp:points (p'∘F)∈conf t.card:=by rw [hu]; exact hx
     apply Subtype.ext
     rw [show ((Z) t)=((Z) (crest f)) from hf.symm ▸ rfl, show t.map u=crest F from (by rw [show crest F=_ from burstM u f,hf])]; rw [peg Q W u S hs f _ (snug _) (by exact canon Q p P t (ht.mono h) _ ((hf).le)),Arise.Bill.pay_f Q (v∘u) p f P (snug _) hx]; let Y:= fun i:Fin t.card=> meaning _ _ (P (f i)); let U:=UV.Free.moment (v∘u∘f) (points (p∘f)) Y; rw [Quills.charge A W F _ (by
          -- InjOn p' mapped on full s
          apply canon W p' P' (crest F) _ _ le_rfl; intro i hi j hj e; obtain ⟨a,rfl⟩:=(exists_fix ..).1 hi; obtain ⟨b,rfl⟩:= (exists_fix ..).1 hj; exact congr_arg F ((show Injective (p' ∘ F) from hp) e)) (u.injective.comp (snug _)), pay_f W v p' F P' _ hp]; swap; · exact u.injective.comp (snug _)
     rw [hu]; have he:UV.Free.moment (v∘F) (points (p∘f)) (fun i=>meaning _ _ (P' (F i)))=U:=congr_arg (UV.Free.moment (v∘F) (points (p∘f))) (funext fun i=> hΦ _ (hk i))
     rw [he]; rfl
private lemma logK (n:ℕ):∀ i⊆T,i.card=n→ jetP A S (cetacea Z i)=cetacea Z' (i.map u):=by
     induction n using Nat.strong_induction_on with
     | h n ih=>
               intro i hv he
               rw [cet,cet]; by_cases h:i.Nonempty; swap; · rw [if_neg h, map_zero,if_neg (fun H=> h (Finset.map_nonempty.mp H))]
               rw [if_pos h,if_pos (Finset.map_nonempty.mpr h),map_sub,inherited Q W u S hs v P P' p p' T ht hm hΦ i hv, map_sum,widenC u,sum_image (Finset.image_injective (markL u) |>.injOn)]
               apply congr_arg; refine sum_congr rfl (fun j hj=>?_); rw[map_prod,Finset.prod_image (markL u|>.injOn)]; exact prod_congr rfl fun k hk=>ih _ (he ▸ Finset.card_lt_card (limit hj hk)) _ ((member (mem_of_mem_erase hj) hk).2.trans hv) rfl
lemma innate(t:Finset I)(h:t⊆T):jetP A S (cetacea Z t)=cetacea Z' (t.map u):=logK Q W u S hs v P P' p p' T ht hm hΦ _ _ h rfl
omit hm hΦ ht hs
variable (X:I→ Patio (A⊕Spine I))(Y: Finset I→ Patio (A⊕Spine I))(X': J→ Patio (A⊕Spine J))(Y': Finset J→ Patio (A⊕Spine J))
-- structural slots; compare unweighted operands or paid occurrence Powers only with declared equality. h exposed.
lemma symbols(hU:∀ i∈T, jetP A S (X i)= X' (u i))(hV:∀ i⊆ T,i.Nonempty→jetP A S (Y i)= Y' (i.map u)): jetP A S (kits T X Y)= kits (T.map u) X' Y':=by
    let φ:= jetP A S; unfold kits; rw [map_mul,map_exp φ φ.toLinearMap.toContinuousLinearMap.continuous,map_exp φ φ.toLinearMap.toContinuousLinearMap.continuous, map_sum,map_sum]; apply congr_arg₂ (·*·)
    · rw [Finset.sum_map]; exact congr_arg _ (sum_congr rfl fun i hi=>hU _ hi)
    rw [erase_v u, sum_image (markL u |>.injOn)]; exact congr_arg _ (sum_congr rfl fun i hi=> hV i (mem_powerset.mp (mem_of_mem_erase hi)) (nonempty_iff_ne_empty.mpr (ne_of_mem_erase hi)))

-- FULL one-cell orientation.Art corrected diagnostic.Y.A independent. No elliptic continuation.
open YM.Massive.Lyre
variable (vA:I→ℕ)(Pa: ∀ i:I, Cups (vA i) (Q i))(XA:I→Alg A)(Xb:J→Alg A) (hP:∀ i:I,Hom (Q i) (XA i))(hB:∀ i:J,Hom (W i) (Xb i))(L:List I)
noncomputable def wordA (P:∀ i:I,Cups (vA i) (Q i))(L:List I): Alg A := chants Q L A (kits L.toFinset (fun i=>emitK Q i (XA i) (hP i)) (fun i=> -cetacea (Arise.Bill.pays (U:=A) Q vA p P) i))
local notation "C!"=> crest
include hm hΦ ht h
lemma figure (hU:L.toFinset=T)(hY: ∀ i∈T,Xb (u i)=XA i)(hk:L.Nodup): wordA W p' v Xb hB P' (L.map u)=wordA Q p (v∘u) XA hP P L:=by
     let X(i:I):Patio (A ⊕ Spine I):= emitK Q i (XA i) (hP i); let F(i: J):=emitK W i (Xb i) (hB i); let g' (i:Finset I): Patio (A⊕Spine I):= -cetacea (pays (U:=A) Q (v∘u) p P) i; let V:=kits L.toFinset X g'
     have hV: ValidPieces A Q L.toFinset V:= by
         refine tracked Q L.toFinset X g' (fun i _=>⟨XA i,rfl⟩) fun i hi=> ?_
         have ht': i.val⊆T := hU ▸ (mem_powerset.mp i.property); let C:=pays (U:=A) Q (v∘u) p P; have hp : Polite Q i.val (cetacea C i.val):=cens_log Q C i.val fun j hj _=>canon Q p P T ht j (hj.trans ht'); exact hp.minus
     obtain ⟨S,hx⟩:= Clover.cards Q W u h; apply Eq.trans _ (readV Q W u S hx L V hk hV)
     unfold wordA; rw [show (L.map u).toFinset=L.toFinset.map u from (by ext; simp [map_eq_image]),hU]; unfold V; rw [hU]; apply congr_arg; symm
     refine symbols u S T X g' F _ ?_ ?_
     · intro i hi; apply Subtype.ext; change changeVars (Matrix.fromBlocks (1:Matrix A A ℂ) 0 0 S) (stake A (burst Q {i}) (XA i))=stake A _ (Xb (u i)); rw [lamp Q W u S hx,hY i hi]
     intro i hi _; change _= -_; unfold g'; rw [map_neg, innate Q W u S hx v P P' p p' T ht hm hΦ _ hi]
end Clover
end YM.MassiveQCD.Sample.Quills
#print axioms YM.MassiveQCD.Sample.Quills.Clover.innate
#print axioms YM.MassiveQCD.Sample.Quills.Clover.figure
