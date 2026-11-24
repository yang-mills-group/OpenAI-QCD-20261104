import YM.Lyre.Locus
import YM.Arise.Sun
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Sample.Quills.Eden
open QCD QCD.Grass QCD.Creek QCD.Cove Function Finset Filter
open MassiveQCD.Ribbon MassiveQCD.Play MassiveQCD.Play.Chamber
open scoped Topology ContDiff BigOperators Classical TensorProduct Matrix.Norms.L2Operator
open YM.Arise.Bill YM.Arise.Count YM.Massive YM.Massive.UV
open MassiveQCD.Play
variable {A B C D I J:Type}[Fintype A][Fintype B][Fintype C][Fintype D][Fintype I][Fintype J]{n:ℕ}
variable (Q:I→Bool)(W:J→Bool)(u:I↪ J)(h:∀ i,W (u i)=Q i)
local notation "PI"=> Spine I
local notation "PJ"=> Spine J
local notation "T" i:arg=> mono (burst Q ({i}:Finset I))
local notation "Tz" i:arg=> mono (burst W ({u i}:Finset J))
variable (M:Matrix A B ℂ)(S: Matrix (Spine I) (Spine J) ℂ)(hP:∀ i:I, staysM S (mono (burst Q {i}))=grade (mono (burst W {u i})))
local notation "θ"=>Matrix.fromBlocks M 0 0 S
variable (s:Fin n→I)(hs:Injective s)
local notation "pin"=> crest s
local notation "rev"=> (Fin.rev :Fin n→ Fin n) -- conflict
local notation "go"=> (u ∘s ∘ rev)
lemma cens_log (Y:Finset I→Patio (A⊕Spine I)) (p:Finset I)(h:∀ i⊆ p,i.Nonempty → Y i∈ VaultP A Q i): cetacea Y p∈ VaultP A Q p:=by
    suffices hv:∀ n:ℕ,∀ v ⊆ p,v.card=n → cetacea Y v∈VaultP A Q v from hv _ p (Subset.refl _) rfl
    intro n; induction n using Nat.strong_induction_on with
    | h n ih=>intro i hi hp; rw [cet]; split; swap; · apply Submodule.zero_mem _
              next he=> refine Submodule.sub_mem _ (h i hi he) (Submodule.sum_mem _ fun j hj=>?_); have hv:=(mem_of_mem_erase hj); rw [show i=j.biUnion id from (mem_filter.mp hv).2.2.1.symm]; exact vp (v:=id) j (fun k hk=> ih _ ((card_lt_card (limit hj hk)).trans_le hp.le) k ((member hv hk).2.trans hi) rfl)
variable (v:J→ℕ)(P: ∀ i:I, Arise.Bill.Cups (v (u i)) (Q i))(P': ∀ i:J, Arise.Bill.Cups (v i) (W i)) (a:Axis) (p:I→ E4) (p':J→E4) (x:E4)
local notation "Z"=> pays (U:=A) Q (v ∘u) p P
local notation "Z'"=> pays (U:=B) W v p' P'
variable (hm:∀ i∈ crest s,p' (u i)= UV.Free.Lyre.crossV a x p i) (hΦ:∀ i∈crest s, Arise.Bill.meaning (v (u i)) (W (u i)) (P' (u i))= UV.adj a (Arise.Bill.meaning (v (u i)) (Q i) (P i))) (hp:Injective (p ∘ s))
lemma canon {w:I→ℕ}(P: ∀ i:I,Cups (w i) (Q i))(X:Finset I)(hx:Set.InjOn p X) (u:Finset I)(h:u⊆X): Polite Q u (Arise.Bill.pays (U:=A) Q w p P u):=by
    let f:= tour u; have hp: points (p ∘ f)∈conf u.card:=by intro i j hij; exact snug u (hx (h (show f i∈u from club u ▸ (exists_fix ..).2 ⟨i,rfl⟩)) (h (show f j∈u from club u ▸ (exists_fix ..).2 ⟨j,rfl⟩)) hij)
    obtain ⟨b,hb⟩:= pay_log (U:=A) Q w p f P (snug u) hp; rw [show crest f=u from club u] at hb; exact ⟨_,hb.symm⟩
include h hs hP hp hm hΦ
lemma placard : antiE θ (Z pin)= Z' ((pin).map u):=by
    have hv:points (p∘s)∈ conf _:= hp; let Y(i:Fin n):= meaning (v (u (s i))) (Q (s i)) (P (s i)); have ht:Set.InjOn p (crest s):=by
       intro i hi j hj; obtain ⟨x,rfl⟩:=(exists_fix s _).1 hi; obtain ⟨y,rfl⟩:=(exists_fix s _).1 hj; intro h; exact congr_arg s (hp h)
    have hA(i:Fin n):s i∈ pin:=(exists_fix s _).2 ⟨i,rfl⟩
    apply Subtype.ext; rw[proceed Q W u h M S hP s hs (canon (w:=v ∘⇑u) Q p P pin ht pin le_rfl)] -- canon args
    let c:= UV.Free.moment (v ∘ u ∘ s) (points (p ∘ s)) Y -- namespace
    rw [show numbered Q A s (Z pin)= c • 1 from pay_f Q (v ∘ u) p s P hs hv,map_smulₛₗ, show staysM M 1=1 from (by simp [staysM, dagger_one])]
    let g:= u∘s∘ (Fin.rev : Fin n→Fin n); have he:(p'∘ g)=UV.Free.Lyre.crossV a x (p ∘ s) ∘ (Fin.rev : Fin n→Fin n):=funext fun i=>hm _ (hA (Fin.rev i)); have hG:points (p' ∘ g)∈conf n:= he.symm ▸ ((UV.Free.Lyre.illuminated a x (p∘s) hp).comp Fin.rev_injective)
    have hV : UV.Free.moment (v∘g) (points (p' ∘ g)) (fun i=>meaning _ _
       (P' (g i))) =star c:=by
       rw [he]; let G i:=UV.adj a (Y (Fin.rev i)); erw [show (fun i:Fin n=> meaning (v (g i)) (W (g i)) (P' (g i))) = G from funext fun i=> hΦ _ (hA _)]; exact UV.Free.Lyre.panel a x (p∘s) (v∘u∘s) Y hp
    rw [← crestM u s]; change _=(Z' (crest g)).val; unfold pays; rw [colored W v p' g P' (u.injective.comp (hs.comp Fin.rev_injective)) hG,hV]; rfl
end YM.MassiveQCD.Sample.Quills.Eden
#print axioms YM.MassiveQCD.Sample.Quills.Eden.placard
#print axioms YM.MassiveQCD.Sample.Quills.Eden.cens_log
