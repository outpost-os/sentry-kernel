use bitflags::bitflags;
use systypes::ResourceHandle;

bitflags! {
    pub struct ResourceHandleBits: u32 {
        const RESOURCE_TYPE = 0b0000_0000_0000_0000_0000_0000_1111;
        const TASK_NS       = 0b0000_0000_0000_1111_1111_1111_0000;
        const RESOURCE_ID   = 0b1111_1111_1111_0000_0000_0000_0000;
    }
}

impl From<ResourceHandleBits> for ResourceHandle {
    fn from(rh: ResourceHandleBits) -> ResourceHandle {
        rh.bits()
    }
}
