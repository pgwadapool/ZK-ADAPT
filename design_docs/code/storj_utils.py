# This is a utility to upload or download files. Set the environment variables 

import os
from uplink_python.errors import StorjException, BucketNotEmptyError, BucketNotFoundError
from uplink_python.module_classes import ListObjectsOptions, Permission, SharePrefix
from uplink_python.uplink import Uplink

def upload_storj(source_file_path, storj_upload_path):
    try:
        # Configuration
        MY_API_KEY = os.getenv("MY_API_KEY")
        MY_SATELLITE = os.getenv("MY_SATELLITE")
        MY_BUCKET = os.getenv("MY_BUCKET")
        MY_ENCRYPTION_PASSPHRASE = os.getenv("MY_ENCRYPTION_PASSPHRASE")

        uplink = Uplink()
        access = uplink.request_access_with_passphrase(MY_SATELLITE, MY_API_KEY, MY_ENCRYPTION_PASSPHRASE)
        project = access.open_project()

        file_handle = open(source_file_path, 'r+b')
        upload = project.upload_object(MY_BUCKET, storj_upload_path)
        upload.write_file(file_handle)
        upload.commit()
        file_handle.close()

        project.close()

    except StorjException as exception:
        print("Exception in upload_storj: ", exception.details)


def download_storj(storj_download_path, destination_file_path):
    try:
        # Configuration
        MY_API_KEY = os.getenv("MY_API_KEY")
        MY_SATELLITE = os.getenv("MY_SATELLITE")
        MY_BUCKET = os.getenv("MY_BUCKET")
        MY_ENCRYPTION_PASSPHRASE = os.getenv("MY_ENCRYPTION_PASSPHRASE")

        uplink = Uplink()
        access = uplink.request_access_with_passphrase(MY_SATELLITE, MY_API_KEY, MY_ENCRYPTION_PASSPHRASE)
        project = access.open_project()

        file_handle = open(destination_file_path, 'w+b')
        download = project.download_object(MY_BUCKET, storj_download_path)
        download.read_file(file_handle)
        download.close()
        file_handle.close()

        project.close()

    except StorjException as exception:
        print("Exception in download_storj: ", exception.details)


