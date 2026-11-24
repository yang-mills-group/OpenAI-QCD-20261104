import YM.QCD.Fount.Spread
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Fount
open Lat Kit Lattice Wilson Function Finset Filter Metric Tree RG Precision Bloch Laurent
open Orbit Flume Sparks Quarry Stationary YM.Next.Free Pine Eyrie Revolve Rudder
open Extra Iteration Placement QCD.Run Work.F08 Work.F03 Exterior Garden Leaf Tee LeafM Port
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator ContDiff Classical
variable {j k N:ℕ}{t p b C:ℝ}{P:Flight j k}{f c:Side}{e:f.val=c.val*P.L.val}
lemma frozen (X:Sheet f)(U:Sheet c)(V:Sheet f)(A: Rail c f)(hu:V∈unitary _)(hp:A=U*A*star V)(h:X=aura V X):
   A*X⁻¹*X⁻¹*Aᴴ= aura U (A*X⁻¹*X⁻¹*Aᴴ):=by
   have he : X⁻¹=aura V X⁻¹ := by rw [invert_W V X hu, ← h]
   let a := A*X⁻¹*X⁻¹*Aᴴ; let b:=U*A*star V; let c:=aura V X⁻¹
   have hd:a=b*c*c*bᴴ:=by unfold a; rw [show X⁻¹=c from he,show A=b from hp]
   change a=aura U a; refine hd.trans ?_; unfold b c a
   unfold aura; rw [Matrix.conjTranspose_mul, ← Matrix.star_eq_conjTranspose,star_star, Matrix.conjTranspose_mul, ← Matrix.star_eq_conjTranspose U]; simp only [Matrix.mul_assoc]; simp_rw [← Matrix.mul_assoc (star V) V, hu.1, Matrix.one_mul]
lemma icing (M:Plan j){s:Signed} : aura (star (scaleA s c)) (barP P e * proton P e)=barP P e*proton P e:=by
   let p:=starTraffic s; let d:=gem s f; let H:= fleetLeft s
   have hp: Glare s (0:Site f) 0 0 d:= gems ..; let r:=sliceL P e; let V:=hues 0 s d p; let U:= hues 0 s (d ∘ r.embed) p
   have h : r.embed 0=0:= map_zero r.root
   have hv:Glare s (r.embed 0) (r.embed 0) (r.embed 0) d:=by simp only [h]; exact hp
   have he:=spin_vault P e hv H (1:Grid f) M -- needs Plan
   have hx:= dual P e hv H (1:Grid f); have hU :Glare s 0 0 0 (d∘ r.embed):= shrouds r hv
   -- rn
   dsimp only at he hx; change vaultF _ P e _ _= _ at he; have hY:pull s (0:Site f) (1:Grid f)=1:=funext fun i=> by simp [pull,Step.read]
   rw [h,hY] at he hx; rw [tree_zero] at he
   rw [← compass_eq hU H]; unfold Garden.barP proton conn; rw [← Matrix.mul_assoc]; exact (congr_arg (aura (star U)) (frozen _ _ _ _ (colour_wheel hp H) hx he)).trans (Orbit.compatible _ _ (colour_wheel hU H))
lemma rawE {A:Plan j} (h : Fractal (driftP P) t C)(hj:4≤j)(hk:4≤k): dust (driftP P) c (1:Grid c)=barP P e * proton P e:=by
   have hp:= h.degree
   have ht:=(tray_model (P:=P) (X:=(0:Cnr f)) (Y:=(0:Cnr c)) (e:=e) hp (paddedP _ hp) (by simp [Iteration.flux,padL,faceCurl,dColor,show parts su 1 (n:=f) 0=(fun _=>0) from rfl]) A hj hk (stoneB hp) h); rw [show (∑' i:Unit,epilogue _ _) = (1:Sheet f) from ?_, Matrix.mul_one] at ht -- inspect
   swap
   · change (∑' i:Unit,epilogue stone (0:Cnr f))= _; rw [litho,tsum_fintype]; simp
   unfold dust; rw [← ht]; apply tsum_congr; intro i
   let W:= driftP P i; have hh:=sector W (0:Cnr c); apply tendsto_nhds_unique ?_ hh; simp [input_zero,W]
end YM.QCD.Fount
