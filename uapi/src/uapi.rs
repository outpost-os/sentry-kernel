use bitflags::bitflags;
use systypes::ResourceHandle;

bitflags! {
    pub struct ResourceHandleBits: u32 {
        const RESOURCE_TYPE = 0b000000000000_000000000000_1111;
        const TASK_NS       = 0b000000000000_111111111111_0000;
        const RESOURCE_ID   = 0b111111111111_000000000000_0000;
    }
}

impl From<ResourceHandleBits> for ResourceHandle {
    fn from(rh: ResourceHandleBits) -> ResourceHandle {
        rh.bits()
    }
}
