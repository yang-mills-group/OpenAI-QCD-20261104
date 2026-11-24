import YM.VStages.Terminus
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
open Relation
section
variable {X:Type*} {R:X→X→Prop}
private lemma view {x y}(h: ReflTransGen R x y):∃ (n:ℕ)(s:ℕ→X), s 0=y ∧ s n=x ∧ ∀ i<n,R (s (i+1)) (s i):=by
    induction h with
    | refl=> exact ⟨0,fun _=> x,rfl,rfl,fun i h=> by omega⟩
    | @tail z w _ hh ih =>
       obtain ⟨n,s,hi,hf,h⟩:= ih
       refine ⟨n+1,(Nat.casesOn (motive:=fun _=>X) · w s),rfl,hf,?_⟩
       intro i hv; cases i
       · exact (show R (s 0) w from hi.symm ▸ hh)
       next i=> exact h _ (by omega)

end

variable (H:ChangeQ→ℕ)(hp:∀ i, LocalRatio (p i))(hc:∀ T:Patch,T.Branches K su)
include hp hc
set_option maxHeartbeats 600000 in
lemma inhabiting (i:ℕ):∃ W:Depot P J p H,W.pillar.nth 0=i:=by
   choose N u using connected P J
   let A(b):=H b+N b+P.lim b
   obtain ⟨E,he,h',hB⟩:= enumerating A i
   have hL (b:ChangeQ)(S:Flight b.old b.new)(hf:A b≤ S.L.val): P.lim b ≤ S.L.val ∧ H b ≤ S.L.val ∧ Century (relation P J b S.patch):=by
       unfold A at hf
       exact ⟨by omega,by omega,u b S.patch (by change _ ≤ S.L.val; omega)⟩
   let r k:= steady (E.nth k); let t:= E.seam
   have hR k:= hL _ _ (h' k); have hT k:= hL _ _ (hB k)
   let R k:= E.rep k; let T k:= E.bridge k
   choose X hx hX using fun k=> (hR k).2.2
   choose Y hY using fun k=> continues ((hT k).2.2) (X (k+1))
   choose n V h0 hS hE using fun k=> view (hX k (Y k))
   have lumber (b:ChangeQ) (S: Flight b.old b.new) (hf:A b≤ S.L.val) (x y:Town)(h:relation P J b S.patch x y):∃ l:Tag P J p, l.node=b ∧ l.L=S.L ∧ l.fromX=x ∧ l.toX=y:=by
       obtain ⟨c,H',Ω,hΩ⟩:=issueW P J x y S (hL b S hf).1 (hp _) (hc _) h
       exact ⟨⟨b,S,x,y,c,H',Ω,hΩ⟩,rfl,rfl,rfl,rfl⟩
   choose S hs hSL hSi hSj using fun k=> lumber (r k) (R k) (h' k) _ _ (hx k)
   choose U hu hUL hUi hUj using fun k (j:Fin (n k))=>lumber (r k) (R k) (h' k) _ _ (hE k j j.isLt)
   choose W hw hWL hWi hWj using fun k=> lumber (t k) (T k) (hB k) _ _ (hY k)
   let Z(k)(l:Fin (n k+1)) : Tag P J p:= Fin.lastCases (W k) (U k) l
   have hz(k): Z k (Fin.last _)=W k:=by simp [Z]
   have hz'(k)(l:Fin (n k)): Z k l.castSucc=U k l:=by simp [Z]
   have hv k : (T k).L.val= 3*(R k).L.val:=by
        change ↑(capPower _) = 3*(capPower _).val; simp [capPower,pow_succ]; ring
   have hv' k : (R (k+1)).L=(T k).L:=by change capPower (k+1+E.start)=capPower _; congr 1; omega
   have hg k j: (Z k j).toX= V k j.val:=by
       refine Fin.lastCases ?_ (fun u=>?_) j
       · rw [hz,hWj]; exact (hS k).symm
       rw [hz',hUj];rfl
   have hJ k j: (Z k j).node.lo=E.nth k:=by
       refine Fin.lastCases ?_ (fun u=>?_) j
       · rw [hz,hw]
       rw [hz',hu]
   have hΛ k j: (R k).L.val ≤ (Z k j).L.val ∧ (Z k j).L.val ≤ 3*(R k).L.val :=by
       refine Fin.lastCases ?_ (fun u=>?_) j
       · rw [hz,hWL,hv]; omega
       rw [hz', hUL]; omega
   refine ⟨⟨E,S,n,Z,fun i=>⟨hs _,hSL _⟩,fun i=>by rw[hSL,hs]; exact (hR i).2.1,fun i=> ?_,fun i=> ?_,fun i j=>?_,fun i=>?_,fun i j=>?_,fun i=>?_,fun i j=>?_⟩,he⟩
   · unfold Tag.NextOK; rw [hs,hSi,hSj]; refine ⟨rfl,rfl,le_rfl,?_⟩; omega
   · unfold Tag.NextOK; rw [hs, hSi, hSL,hg,hJ]; exact ⟨rfl,(h0 i).symm,hΛ ..⟩
   · unfold Tag.NextOK; rw [hz' i j,hu,hUL,hUi,hJ,hg]; exact ⟨rfl,rfl,hΛ ..⟩
   · unfold Tag.NextOK; rw [hz,hw,hWi,hWL,hSL,hv',hs,hSj]; exact ⟨E.meets i,rfl,le_rfl,by omega⟩
   · rw [hz',hu,hUL,hs,hSL]; exact ⟨rfl,rfl⟩
   · rw [hz]; exact ⟨hw _,hWL _⟩
   refine Fin.lastCases ?_ (fun u=>?_) j
   · rw [hz,hw,hWL]; exact (hT i).2.1
   rw [hz',hu,hUL]; exact (hR i).2.1
#print axioms inhabiting
end YM.QCD.Acre.Stratum.MarchQ
