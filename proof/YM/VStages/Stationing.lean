import YM.VStages.Stroll
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Acre.Stratum.MarchQ
open Function Lattice RG Laurent Bloch Matrix Metric Precision Wilson Bid Craft Exterior Filter
open YM.Next.Free YM.Work YM.Further.PhysicalPeriodLimitF933
open WilsonStartup Design Change Extra.Iteration Stationary Tree Raft Garden Transfer Orbit Sparks Fog Birth Raft.ParcelR
open Flume Fog.Mist YM.Massive.Stratum Push ConnectedActivityE6 Pressure Pressure.Stores
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {j t k i l n N: ℕ}{K:KernelChoices}{p:ChangeQ→ChartRatio su}{h s:ℕ→ℕ}
 (P:Docket K h s)(J:(i:ℕ)→Plan (rank i))
open ChangeQ

-- parametric continue factors. Use independent corridor chunks run to and through origin
-- counts. `Pad` chosen after β etc imposes any observations durations.

structure Track (P:Docket K h s)(J:(i:ℕ)→Plan (rank i))(p:ChangeQ→ChartRatio su) (gate:ChangeQ→ℕ) where
   beam (i:ℕ):Tag P J p
   nexts i: (beam i).NextOK (beam (i+1))
   room i: gate (beam i).node ≤ (beam i).L.val
   powers i: ∃ j:ℕ, (beam i).L= (3:Side)^j
   free : Tendsto (fun i=> (beam i).node.lo) atTop atTop
   openL : Tendsto (fun i=> (beam i).L.val) atTop atTop
   stops : ∀ i, ∃ j,i ≤ j ∧ (beam j).node=steady (beam j).node.lo
namespace Depot
variable {P J} {gate:ChangeQ→ℕ}(D:Depot P J p gate)
-- charge a startup budget also for the first rep of next stage.
def Needs (f:Tag P J p→ℕ) (k:ℕ):ℕ:= (Finset.univ.sup (f ∘ D.blockEnd k)) + f (D.fixed (k+1))
variable (f:Tag P J p→ℕ)(pad : ℕ→ℕ→ℕ)

def starts (D:Depot P J p gate) (f:Tag P J p→ℕ) (pad : ℕ→ℕ→ℕ): ℕ→ℕ
   | 0=>0
   | k+1=> (starts D f pad k+D.Needs f k+pad k (starts D f pad k)+1)+(D.rounds k+1)
abbrev rear (k:ℕ) := D.starts f pad k + D.Needs f k +pad k (D.starts f pad k)+1
local notation "b"=>D.starts f pad
local notation "v"=> D.rear f pad
lemma plus (i:ℕ) : b (i+1)=v i+(D.rounds i+1):=rfl
lemma starts_up : StrictMono b:= strictMono_nat_of_lt_succ fun i=> by rw [plus]; unfold rear; omega
lemma adj(i:ℕ): b i<v i ∧ v i < b (i+1):=by
  constructor
  · unfold rear; omega
  rw [plus]; omega
abbrev Lead(k i:ℕ): Prop:= b k≤ i∧ i< v k
abbrev Tail(k i:ℕ): Prop:= v k ≤ i∧ i<b (k+1)
abbrev At (k i:ℕ) := b k≤ i ∧ i<b (k+1)

lemma segment(i:ℕ) : ∃ j:ℕ, D.At f pad j i:=by
    induction i with
    | zero=> exact ⟨0, le_rfl,by
                     have h:=D.starts_up f pad (show 0 < 1 from by omega); exact h⟩
    | succ i ih=>
       obtain ⟨j,h,h'⟩:=ih
       by_cases hp:i+1<b (j+1); exact ⟨j,le_trans h (by omega),hp⟩
       have hi:i+1=b (j+1):=by omega
       exact ⟨j+1,hi ▸ le_rfl, hi ▸ D.starts_up f pad (show j+1< j+1+1 from by omega)⟩
def reaches (i:ℕ):= (D.segment f pad i).choose
lemma reachP (i:ℕ): D.At f pad (D.reaches f pad i) i:=(D.segment f pad i).choose_spec
lemma map_at (k i:ℕ)(h:D.At f pad k i): D.reaches f pad i=k:=by
    let j:=D.reaches f pad i; obtain ⟨hX,hP⟩:= h; obtain ⟨h,hU⟩:=D.reachP f pad i; change j=k; change b j≤ i at h; change i<b (j+1) at hU
    obtain H|H|H:=lt_trichotomy j k; · have hh:=D.starts_up f pad|>.monotone (show j+1 ≤ k from H); omega
    · exact H
    have hh:=D.starts_up f pad|>.monotone (show k+1 ≤ j from H); omega
lemma contained (k i:ℕ)(h:D.Lead f pad k i):D.At f pad k i:= ⟨h.1,h.2.trans (D.adj f pad k).2⟩
lemma supported (k i:ℕ)(h:D.Tail f pad k i): D.At f pad k i:= ⟨(D.adj f pad k).1.le.trans h.1,h.2⟩
lemma on_tail {j i:ℕ}(h:D.Tail f pad j i): i-v j< D.rounds j+1:= by obtain ⟨h,h'⟩:=h; rw [plus] at h'; omega
noncomputable def current (i:ℕ): Tag P J p:=
    let j:=D.reaches f pad i
    if h: D.Tail f pad j i then D.blockEnd j ⟨i-v j, D.on_tail f pad h⟩ else D.fixed j
lemma at_lead {j i:ℕ}(h:D.Lead f pad j i): D.current f pad i= D.fixed j:=by unfold current; rw [map_at D f pad _ _ (D.contained f pad j i h)]; dsimp only; apply dif_neg; exact fun ht=>h.2.not_ge ht.1
lemma recorded {j i:ℕ}(h:D.Tail f pad j i): D.current f pad i = D.blockEnd j ⟨i-v j, D.on_tail f pad h⟩:=by
     unfold current; rw [map_at D f pad _ _ (D.supported f pad j i h)]; exact dif_pos h
lemma initial (j:ℕ): D.current f pad (b j)=D.fixed j:= D.at_lead f pad (show D.Lead f pad j (b j) from ⟨le_rfl,(D.adj f pad j).1⟩)
lemma brief {i:ℕ}: let j:=D.reaches f pad i; D.Lead f pad j i ∨ D.Tail f pad j i:= by intro j; obtain ⟨h,h'⟩:=D.reachP f pad i; by_cases H:i<v j; exact Or.inl ⟨h,H⟩; exact Or.inr ⟨Nat.le_of_not_lt H,h'⟩
local notation "g"=>D.current f pad
lemma funds (i:ℕ): gate (g i).node ≤ (g i).L.val ∧ f (g i) ≤ i+f (D.fixed 0):=by
  obtain h|h := D.brief f pad (i:=i)
  · rw [at_lead D f pad h]; refine ⟨D.resource _,?_⟩
    let k:=D.reaches f pad i; have he:b k ≤ i:=h.1; change f (D.fixed k) ≤ _
    generalize hz:k=t at he ⊢; cases t with
    | zero=> omega
    | succ k=> have hz:f (D.fixed (k+1))≤ v k:=by unfold rear Needs; omega
               rw [plus] at he; omega
  rw [recorded D f pad h]; refine ⟨D.paid _ _,?_⟩
  let k:=D.reaches f pad i; let j:Fin (D.rounds k+1):= ⟨i-v k, D.on_tail f pad h⟩
  have ht: f (D.blockEnd k j) ≤ D.Needs f k := le_trans (show _ ≤ Finset.univ.sup (f∘D.blockEnd k) from Finset.le_sup (f:=f ∘ _) (Finset.mem_univ j)) (by unfold Needs; omega)
  have hr:v k ≤ i := h.1; unfold rear at hr; change f (D.blockEnd k j) ≤ _; omega
lemma pace (i:ℕ): (g i).NextOK (g (i+1)):=by
  obtain h|h:= D.brief f pad (i:=i)<;> let k:= D.reaches f pad i
  · rw [at_lead D f pad h]
    have he: i<v k:=h.2
    rcases lt_or_eq_of_le (show i+1 ≤ v k from he) with hv|hv
    · rw [at_lead D f pad (show D.Lead f pad k (i+1) from ⟨h.1.trans (by omega),hv⟩)]; exact D.visits _
    have ht: D.Tail f pad k (i+1):= hv ▸ ⟨le_rfl,(D.adj f pad k).2⟩
    rw [recorded D f pad ht]; convert D.stares k using 1
    congr 1; apply Fin.ext; change i+1-v k=0; omega
  have he:i ≥ v k:= h.1
  have hh:i < b (k+1):= h.2
  rcases lt_or_eq_of_le (show i+1≤b (k+1) from hh) with hu|hu
  · rw [recorded D f pad h, recorded D f pad (show D.Tail f pad k (i+1) from ⟨by omega,hu⟩)]; rw [plus] at hu
    let u:Fin (D.rounds k):=⟨i-v k,by omega⟩; convert D.progresses k u using 1
    congr 1; apply congrArg (D.blockEnd k); apply Fin.ext; change i+1-v k=i-v k+1; omega
  rw [recorded D f pad h, hu, D.initial f pad]; have hv:= D.arrives k
  rw [plus] at hu; convert hv using 1
  congr 1; apply Fin.ext; change i-v k=D.rounds k; omega
lemma steep (i j): (g i).NextOK (g j) → (g i).node.lo ≤ (g j).node.lo := by
    intro h; rw [← h.1]; have hf:= (g i).node.path; omega
noncomputable def track:Track P J p gate where
   beam:=g
   nexts:=D.pace f pad
   room i:= (D.funds f pad i).1
   powers i:=by
      obtain h|h:=D.brief f pad (i:=i)
      · rw [at_lead D f pad h,(D.tall _).2]; exact ⟨_,rfl⟩
      rw [recorded D f pad h]; generalize ((⟨_,D.on_tail _ _ h⟩:Fin _)) = j
      let k:=D.reaches f pad i
      refine Fin.lastCases ?_ (fun j=>?_) j
      · rw [(D.changeNode k).2]; exact ⟨_,rfl⟩
      rw [(D.dates k j).2,(D.tall _).2]; exact ⟨_,rfl⟩
   free:=by
      have hm:Monotone (fun i=>(g i).node.lo):= monotone_nat_of_le_succ fun i=> D.steep f pad _ _ (D.pace f pad i)
      refine Filter.tendsto_atTop.mpr (fun i=>?_)
      obtain ⟨k,hk⟩:= (D.pillar.endless.eventually_ge_atTop i).exists
      filter_upwards [eventually_ge_atTop (b k)] with j hj
      have hx:= hm hj; simp only at hx; rw [initial,(D.tall k).1] at hx; exact le_trans hk hx
   openL :=by
      have hm:Monotone (fun i=>(g i).L.val):= monotone_nat_of_le_succ fun i=> (D.pace f pad i).2.2.1
      refine Filter.tendsto_atTop.mpr (fun i=>?_)
      obtain ⟨k,hk⟩:= ((movePower.comp (tendsto_add_atTop_nat D.pillar.start)).eventually_ge_atTop i).exists
      filter_upwards [eventually_ge_atTop (b k)] with j hj
      have hx:= hm hj; simp only at hx; rw [initial,(D.tall k).2] at hx; exact hk.trans hx
   stops i:= ⟨b i, (D.starts_up f pad).id_le i, by rw [D.initial,(D.tall _).1]⟩
end Depot
end YM.QCD.Acre.Stratum.MarchQ
